"""Fresh build orchestration with durable, content-bound command evidence."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

from . import checks, metadata
from .common import (EvidenceError, canonical_digest, code_only, digest,
                     digest_bytes, input_snapshot, mathematical_sources, now,
                     portable_paths, read_json, regular_project_file, save_json, tool_snapshot)


class Runner:
    def __init__(self, root: Path, run_id: str, *, static_only: bool = False,
                 skip_build: bool = False, timeout: int = 3600):
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,95}", run_id):
            raise EvidenceError("run-id must be 1–96 safe ASCII filename characters")
        self.root, self.run_id = root.resolve(), run_id
        self.folder = self.root / "fidelity/runs" / run_id
        if self.folder.exists():
            raise EvidenceError(f"Refusing to reuse evidence directory: {self.folder}")
        self.folder.mkdir(parents=True)
        self.static_only, self.skip_build, self.timeout = static_only, skip_build, timeout
        self.env = os.environ.copy()
        toolchain = self.root / ".tooling/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin"
        if toolchain.is_dir():
            self.env["ELAN_HOME"] = str(self.root / ".tooling/elan")
            self.env["PATH"] = str(toolchain) + os.pathsep + self.env.get("PATH", "")
        self.report = {"schema_version": 1, "run_id": run_id, "started_at": now(),
                       "finished_at": None, "overall": "running", "root": str(self.root),
                       "mode": {"static_only": static_only, "skip_build": skip_build},
                       "inputs": {}, "tools": {}, "steps": {}, "commands": [],
                       "dimensions": {}, "limitations": [], "unresolved": []}
        self.flush()

    def flush(self) -> None:
        save_json(self.folder / "report.json", self.report)

    def step(self, name: str, function, *args):
        started, tick = now(), time.monotonic()
        self.report["steps"][name] = {"status": "running", "started_at": started}
        self.flush()
        try:
            details = function(*args)
            summary = details
            if name == "environment_validation":
                summary = {"validated_declarations": len(details)}
            elif name == "specifications":
                summary = {side: {"atoms": len(atoms)} for side, atoms in details.items()}
            elif name == "canonical_coverage":
                summary = {"claims": len(details["claims"]), "coverage": details["coverage"]}
            elif name == "reviews":
                summary = {field: value for field, value in details.items() if field != "per_claim"}
            record = {"status": "pass", "details": summary}
        except (EvidenceError, OSError, ValueError, KeyError, TypeError) as exc:
            message = str(exc)
            status = "blocked" if message.startswith(("Missing", "Cannot read", "No such", "Tool unavailable")) else "fail"
            record = {"status": status, "reason": message}
            details = None
        record.update(started_at=started, finished_at=now(),
                      duration_seconds=round(time.monotonic() - tick, 3))
        self.report["steps"][name] = record
        self.flush()
        return details

    def skip(self, name: str, reason: str) -> None:
        self.report["steps"][name] = {"status": "skipped", "reason": reason}
        self.flush()

    def command(self, name: str, argv: list[str], cwd: Path | None = None) -> dict:
        cwd = self.root if cwd is None else cwd
        index = len(self.report["commands"])
        prefix = f"{index:03d}-{name}"
        stdout, stderr = self.folder / f"{prefix}.stdout.log", self.folder / f"{prefix}.stderr.log"
        started, tick = now(), time.monotonic()
        record = {"name": name, "argv": argv, "cwd": str(cwd), "started_at": started,
                  "input_snapshot_sha256": self.report.get("snapshot_sha256"),
                  "tool_snapshot_sha256": self.report.get("tools_sha256"),
                  "exit_code": None, "status": "running",
                  "stdout": stdout.relative_to(self.root).as_posix(),
                  "stderr": stderr.relative_to(self.root).as_posix()}
        self.report["commands"].append(record)
        self.flush()
        with stdout.open("wb") as out, stderr.open("wb") as err:
            try:
                result = subprocess.run(argv, cwd=cwd, env=self.env, stdin=subprocess.DEVNULL,
                                        stdout=out, stderr=err, timeout=self.timeout, check=False)
                record.update(exit_code=result.returncode,
                              status="pass" if result.returncode == 0 else "fail")
            except FileNotFoundError as exc:
                record.update(status="blocked", reason=f"Tool unavailable: {exc}")
            except subprocess.TimeoutExpired:
                record.update(status="blocked", reason=f"Command exceeded {self.timeout} seconds")
            except OSError as exc:
                record.update(status="blocked", reason=str(exc))
            except BaseException:
                record.update(status="blocked", reason="Command interrupted")
                raise
            finally:
                record.update(finished_at=now(), duration_seconds=round(time.monotonic() - tick, 3))
                out.flush()
                err.flush()
                record.update(stdout_sha256=digest(stdout), stderr_sha256=digest(stderr))
                # Preserve diagnostics produced before a failed/blocked tool
                # exit too; a success-only output list would hide counterexamples.
                generated = {"compiled-semantic-mutations": "semantic_mutations.json",
                             "exact-experiments": "experiments.json",
                             "environment-export": "environment.raw.json"}.get(name)
                if generated and (self.folder / generated).is_file():
                    artifact = self.folder / generated
                    record["artifacts"] = [{"path": artifact.relative_to(self.root).as_posix(),
                                            "sha256": digest(artifact)}]
                self.flush()
        return record

    def must_command(self, name: str, argv: list[str], cwd: Path | None = None) -> dict:
        record = self.command(name, argv, cwd)
        if record["status"] != "pass":
            prefix = "Tool unavailable" if record["status"] == "blocked" else "Command failed"
            raise EvidenceError(f"{prefix}: {name}; exit={record['exit_code']}; see {record['stderr']}")
        return record

    def snapshot(self) -> dict:
        inputs, tools = input_snapshot(self.root), tool_snapshot(self.root)
        self.report.update(inputs=inputs, tools=tools, snapshot_sha256=canonical_digest(inputs),
                           tools_sha256=canonical_digest(tools))
        self.report["review_and_issue_inputs"] = self.auxiliary_inputs()
        save_json(self.folder / "inputs.json", {"schema_version": 1, "inputs": inputs,
                                                "snapshot_sha256": canonical_digest(inputs)})
        return {"input_files": len(inputs), "tool_files": len(tools)}

    def auxiliary_inputs(self) -> dict:
        paths = [path for folder in ("fidelity/reviews", "fidelity/issues")
                 for path in (self.root / folder).rglob("*.json")]
        return {path.relative_to(self.root).as_posix(): digest(regular_project_file(
            self.root, path.relative_to(self.root).as_posix())) for path in sorted(paths)}

    def stability(self) -> dict:
        current, tools = input_snapshot(self.root), tool_snapshot(self.root)
        if current != self.report["inputs"]:
            changed = sorted(name for name in set(current) | set(self.report["inputs"])
                             if current.get(name) != self.report["inputs"].get(name))
            raise EvidenceError(f"Source mutation invalidated this run: {changed}")
        if tools != self.report["tools"]:
            raise EvidenceError("Checker or Lean export/certificate tools changed during this run")
        if self.auxiliary_inputs() != self.report.get("review_and_issue_inputs", {}):
            raise EvidenceError("Review or issue artifacts changed during this run")
        issue_hashes = self.report.get("issue_inputs")
        if issue_hashes is not None:
            current_issues = {path.relative_to(self.root).as_posix(): digest(path)
                              for path in sorted((self.root / "fidelity/issues").rglob("*.json"))}
            if current_issues != issue_hashes:
                raise EvidenceError("Current issue evidence changed during this run")
        return {"snapshot_sha256": canonical_digest(current), "tools_sha256": canonical_digest(tools)}

    def tools(self) -> dict:
        paths = {name: shutil.which(name, path=self.env.get("PATH")) for name in ("lake", "git", "python3")}
        missing = [name for name, path in paths.items() if path is None]
        if missing:
            raise EvidenceError(f"Tool unavailable: {', '.join(missing)}")
        self.lake = paths["lake"]
        sibling = Path(self.lake).with_name("lean")
        self.lean = str(sibling) if sibling.is_file() else shutil.which("lean", path=self.env.get("PATH"))
        if self.lean is None:
            raise EvidenceError("Tool unavailable: fixed Lean executable")
        paths["lean"] = self.lean
        record = self.must_command("lean-version", [self.lake, "env", "lean", "--version"])
        text = (self.root / record["stdout"]).read_text(encoding="utf-8")
        pin = regular_project_file(self.root, "lean-toolchain").read_text().strip()
        if not pin.startswith("leanprover/lean4:v"):
            raise EvidenceError(f"Unsupported fixed Lean toolchain: {pin}")
        expected = pin.split(":v", 1)[1]
        match = re.search(r"Lean \(version ([^,\s)]+)", text)
        if not match or match.group(1) != expected:
            raise EvidenceError(f"Lean version differs from fixed toolchain {pin}: {text.strip()}")
        return {"executables": paths, "lean_toolchain": pin, "lean_version": text.strip()}

    def compiled_semantic_mutations(self) -> dict:
        script = regular_project_file(self.root, "scripts/fidelity/semantic_mutations.py")
        output = self.folder / "semantic_mutations.json"
        self.must_command("compiled-semantic-mutations", [sys.executable, str(script),
                          "--lean", self.lean, "--output", str(output)])
        result = checks.semantic_mutations(self.root, read_json(output))
        result["output"] = {"path": output.relative_to(self.root).as_posix(), "sha256": digest(output)}
        return result

    def review_check(self, claims, env, exported, roles):
        collector = self.report.setdefault("review_claim_evidence", {})
        return checks.reviews(self.root, self.report["inputs"], claims, env,
                              exported["declarations_sha256"],
                              validated_metadata_roles=roles, claim_evidence=collector)

    def route_check(self, env, claims):
        from .route_dependencies import validate
        return validate(self.root, env, claims)

    def dependencies(self) -> dict:
        manifest = read_json(self.root / "lake-manifest.json")
        packages = manifest.get("packages")
        if not isinstance(packages, list) or not packages:
            raise EvidenceError("Missing locked dependency manifest packages")
        result = {}
        for package in packages:
            if not isinstance(package, dict) or package.get("type") != "git":
                raise EvidenceError("Unsupported unlocked dependency kind")
            name, expected = package.get("name"), package.get("rev")
            if not isinstance(name, str) or not re.fullmatch(r"[\w-]+", name):
                raise EvidenceError("Malformed locked package name")
            if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{40}", expected):
                raise EvidenceError(f"Dependency is not fixed to a commit: {name}")
            path = self.root / ".lake/packages" / name
            if not path.is_dir():
                raise EvidenceError(f"Missing pinned dependency checkout: {name}")
            record = self.must_command(f"dependency-{name}", ["git", "-C", str(path), "rev-parse", "HEAD"])
            actual = (self.root / record["stdout"]).read_text().strip()
            if actual != expected:
                raise EvidenceError(f"Locked dependency checkout changed: {name}: {actual} != {expected}")
            # A dirty tracked dependency can retain the same HEAD, so HEAD alone
            # is insufficient. Untracked compiled caches are intentionally fine.
            dirty = self.must_command(f"dependency-clean-{name}", ["git", "-C", str(path), "diff", "--exit-code", "HEAD", "--"])
            result[name] = {"revision": actual, "tracked_tree_clean": dirty["exit_code"] == 0}
        return result

    def build_math(self, project: Path, label: str) -> dict:
        # Never let a submitted project .olean/trace establish current evidence.
        # Dependency caches are checked separately and intentionally retained.
        artifacts = project / ".lake/build"
        if (project / ".lake").is_symlink() or artifacts.is_symlink():
            raise EvidenceError("Project build directory must not be a symlink")
        if artifacts.exists():
            if not artifacts.is_dir() or not artifacts.resolve().is_relative_to(project.resolve()):
                raise EvidenceError("Project build directory escaped the project")
            shutil.rmtree(artifacts)
        modules = [path.relative_to(project).as_posix()[:-5].replace("/", ".")
                   for path in mathematical_sources(project)
                   if path.relative_to(project).parts[0] != "FidelityLean"]
        self.must_command(label, [self.lake, "build", *[f"+{module}" for module in modules]], project)
        return {"modules": len(modules), "targets": modules, "project_artifacts_cleared_before_build": True}

    def fidelity_order(self, project: Path) -> list[Path]:
        paths = {path.relative_to(project).as_posix()[:-5].replace("/", "."): path
                 for path in (project / "FidelityLean").rglob("*.lean")}
        if not {"FidelityLean.Export", "FidelityLean.Spec"}.issubset(paths):
            raise EvidenceError("Missing FidelityLean.Export or independent FidelityLean.Spec implementation")
        if not any(path.stem.endswith("Certificates") for path in paths.values()):
            raise EvidenceError("Missing compiled certificate module sources")
        result, active, done = [], set(), set()
        def visit(name):
            if name in active:
                raise EvidenceError(f"Cyclic Fidelity imports: {name}")
            if name in done:
                return
            if name not in paths:
                raise EvidenceError(f"Missing Fidelity imported module: {name}")
            active.add(name)
            code = code_only(paths[name].read_text(encoding="utf-8"))
            for imported in re.findall(r"^\s*import\s+(FidelityLean(?:\.[\w]+)+)", code, re.M):
                visit(imported)
            active.remove(name)
            done.add(name)
            result.append(paths[name])
        for name in sorted(paths):
            visit(name)
        return result

    def compile_fidelity(self, project: Path, label: str) -> dict:
        modules = []
        for path in self.fidelity_order(project):
            relative = path.relative_to(project)
            output = project / ".lake/build/lib/lean" / relative.with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            self.must_command(f"{label}-{path.stem}", [self.lake, "env", "lean", "-o", str(output), str(relative)], project)
            if not output.is_file():
                raise EvidenceError(f"Compiled Fidelity artifact missing: {relative}")
            modules.append(relative.as_posix())
        return {"compiled_modules": modules}

    def export(self) -> dict:
        raw = self.folder / "environment.raw.json"
        modules = [path.relative_to(self.root).as_posix()[:-5].replace("/", ".")
                   for path in mathematical_sources(self.root)]
        modules.extend(path.relative_to(self.root).as_posix()[:-5].replace("/", ".")
                       for path in self.fidelity_order(self.root) if path.name != "Export.lean")
        modules = list(dict.fromkeys(modules))
        self.must_command("environment-export", [self.lake, "env", "lean", "--run", "FidelityLean/Export.lean", str(raw), *modules])
        data = read_json(raw)
        if not isinstance(data.get("decls"), list) or not data["decls"]:
            raise EvidenceError("Missing declarations in fresh environment export")
        # Lean's native expression hash is retained, but the portable type_hash
        # reviewed by humans is SHA-256 of exactly the exported UTF-8 type text.
        for item in data["decls"]:
            if not isinstance(item, dict) or not isinstance(item.get("type"), str):
                raise EvidenceError("Malformed fresh environment declaration type")
            if "type_hash" in item:
                item["native_type_hash"] = item["type_hash"]
            item["type_hash"] = digest_bytes(item["type"].encode("utf-8"))
        data["run_id"] = self.run_id
        data["snapshot_sha256"] = self.report["snapshot_sha256"]
        data["declarations_sha256"] = canonical_digest(data["decls"])
        save_json(self.folder / "environment.json", data)
        return {"raw_sha256": digest(raw), "sha256": digest(self.folder / "environment.json"),
                "path": (self.folder / "environment.json").relative_to(self.root).as_posix(),
                "declarations": len(data["decls"]), "declarations_sha256": data["declarations_sha256"]}

    def exact_experiments(self, claims: dict) -> dict:
        script = regular_project_file(self.root, "scripts/fidelity/exact_experiments.py")
        output = self.folder / "experiments.json"
        self.must_command("exact-experiments", [sys.executable, str(script), "--output", str(output)])
        result = checks.experiments(self.root, read_json(output), claims)
        result["output"] = {"path": output.relative_to(self.root).as_posix(), "sha256": digest(output)}
        return result

    def source_archive(self, label: str) -> tuple[Path, dict]:
        from .archive import inventory as archive_inventory
        selected = archive_inventory(self.root)
        output = self.folder / f"reproduction-{label}-source.zip"
        inventory = {}
        with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED) as archive:
            for name, expected in selected.items():
                path = regular_project_file(self.root, name)
                data = path.read_bytes()
                if digest_bytes(data) != expected:
                    raise EvidenceError(f"Archive source/evidence changed before writing: {name}")
                inventory[name] = digest_bytes(data)
                info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                info.external_attr = 0o100644 << 16
                archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED)
        save_json(self.folder / f"reproduction-{label}-manifest.json", inventory)
        return output, inventory

    def reproduce(self, label: str, *, from_archive: bool = False) -> dict:
        # Use the same source selection for both independent reproductions.
        # Each ZIP is generated in this run, never supplied by a previous log.
        archive, inventory = self.source_archive(label)
        with tempfile.TemporaryDirectory(prefix=f"affine-fidelity-{label}-") as temporary:
            project = Path(temporary) / "project"
            project.mkdir()
            if from_archive:
                with zipfile.ZipFile(archive) as source:
                    source.extractall(project)
            else:
                for name in inventory:
                    target = project / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(regular_project_file(self.root, name), target)
            for name, expected in inventory.items():
                if digest(regular_project_file(project, name)) != expected:
                    raise EvidenceError(f"Reproduction source copy hash mismatch: {name}")
            if input_snapshot(project) != self.report["inputs"]:
                raise EvidenceError("Independent reproduction source snapshot differs from audited inputs")
            packages = self.root / ".lake/packages"
            if not packages.is_dir():
                raise EvidenceError("Missing pinned package cache for independent reproduction")
            (project / ".lake").mkdir()
            # Only locked, checked dependency checkouts are shared. Project
            # artifacts are built in an entirely new .lake/build directory.
            (project / ".lake/packages").symlink_to(packages, target_is_directory=True)
            build = self.build_math(project, f"{label}-math")
            fidelity = self.compile_fidelity(project, label)
            built = []
            for path in mathematical_sources(project):
                relative = path.relative_to(project).with_suffix(".olean")
                artifact = project / ".lake/build/lib/lean" / relative
                if not artifact.is_file() or artifact.is_symlink():
                    raise EvidenceError(f"Clean project module was not rebuilt: {relative}")
                built.append({"module": relative.as_posix(), "sha256": digest(artifact)})
            return {"mechanism": "zip-extract" if from_archive else "fresh-source-copy",
                    "source_archive_sha256": digest(archive), "source_files": len(inventory),
                    "source_manifest": {"path": (self.folder / f"reproduction-{label}-manifest.json").relative_to(self.root).as_posix(),
                                        "sha256": digest(self.folder / f"reproduction-{label}-manifest.json")},
                    "shared_locked_dependencies_only": True, "project_build_was_empty": True,
                    "math": build, "fidelity": fidelity, "artifacts": built}

    def finish(self) -> int:
        statuses = {name: step["status"] for name, step in self.report["steps"].items()}
        def group(names):
            values = [statuses.get(name, "blocked") for name in names]
            return "pass" if values and all(value == "pass" for value in values) else (
                "fail" if "fail" in values else "blocked")
        semantic = group(["reviews", "canonical_coverage", "specifications", "issues", "metadata_reviews", "source_stability"])
        self.report["dimensions"] = {
            "object_correspondence": semantic,
            "statement_correspondence": semantic,
            "route_correspondence": group(["reviews", "route_dependencies", "canonical_coverage", "metadata_reviews", "source_stability"]),
            "kernel": group(["baseline", "source_audit", "tools", "dependencies", "build",
                             "pure_spec_sources", "fidelity_compile", "environment_export", "environment_validation",
                             "certificates", "source_stability"]),
            "reproduction": group(["clean_rebuild", "archive_rebuild", "exact_experiments", "semantic_mutations", "source_stability"])}
        if self.static_only or self.skip_build:
            self.report["dimensions"]["kernel"] = "blocked"
            self.report["dimensions"]["reproduction"] = "blocked"
        def combine(values):
            return "fail" if "fail" in values else ("pass" if values and all(value == "pass" for value in values) else "blocked")
        self.report["claim_status"] = {}
        source_bound = statuses.get("canonical_coverage") == "pass" and statuses.get("source_stability") == "pass"
        critical_routes = set()
        route_manifest = self.root / "fidelity/route_requirements.json"
        if route_manifest.is_file():
            try:
                critical_routes = {rule["claim"] for rule in read_json(route_manifest).get("rules", [])}
            except (EvidenceError, TypeError, KeyError):
                pass
        for key, claim in getattr(self, "canonical_claims", {}).items():
            verified = self.report.get("review_claim_evidence", {}).get(key, {})
            dimensions = {dimension: verified.get(dimension, {}).get("status", "blocked") for dimension in checks.DIMENSIONS}
            if not source_bound:
                dimensions = {dimension: "blocked" if status == "pass" else status for dimension, status in dimensions.items()}
            route_status = verified.get("route", {}).get("status", "blocked")
            if not source_bound and route_status == "pass":
                route_status = "blocked"
            if key in critical_routes:
                route_status = combine([route_status, statuses.get("route_dependencies", "blocked")])
            self.report["claim_status"][key] = {"declarations": claim.get("declarations", []),
                "semantic_dimensions": dimensions, "verified_evidence": verified,
                "dimensions": {"object_correspondence": dimensions["objects"],
                               "statement_correspondence": combine([dimensions[field] for field in checks.DIMENSIONS if field != "objects"]),
                               "route_correspondence": route_status,
                               "kernel": self.report["dimensions"]["kernel"] if claim.get("declarations") else "blocked",
                               "reproduction": self.report["dimensions"]["reproduction"]}}
        common = group(["canonical_coverage", "specifications", "metadata_reviews", "issues", "source_stability"])
        for dimension in ("object_correspondence", "statement_correspondence", "route_correspondence"):
            values = [item["dimensions"][dimension] for item in self.report["claim_status"].values()]
            if dimension == "route_correspondence":
                values.append(statuses.get("route_dependencies", "blocked"))
            self.report["dimensions"][dimension] = combine([common, combine(values)])
        required = {"snapshot", "protocol", "baseline", "source_audit", "specifications", "canonical_coverage",
                    "tools", "dependencies", "build", "fidelity_compile", "environment_export",
                    "environment_validation", "reviews", "exact_experiments", "clean_rebuild",
                    "archive_rebuild", "source_stability", "issues", "metadata_reviews", "pure_spec_sources",
                    "certificates", "semantic_mutations", "route_dependencies"}
        unresolved = [{"step": name, "status": statuses.get(name, "blocked"),
                       "reason": self.report["steps"].get(name, {}).get("reason", "Required evidence absent")}
                      for name in sorted(required) if statuses.get(name) != "pass"]
        incomplete_claims = [key for key, item in self.report["claim_status"].items()
                             if any(value != "pass" for value in item["dimensions"].values())]
        self.report["steps"]["claim_dimensions"] = {
            "status": "pass" if self.report["claim_status"] and not incomplete_claims else "blocked",
            "details": {"claims": len(self.report["claim_status"]), "incomplete_claims": len(incomplete_claims)}}
        if not self.report["claim_status"] or incomplete_claims:
            unresolved.append({"step": "claim_dimensions", "status": "blocked",
                "reason": (f"Claim-specific verified evidence is incomplete: {len(incomplete_claims)} claims; "
                           f"examples: {incomplete_claims[:8]}" if incomplete_claims else "No canonical claims with verified evidence")})
        self.report["unresolved"] = unresolved
        passed = not unresolved and not self.static_only and not self.skip_build
        self.report["overall"] = "pass" if passed else (
            "fail" if any(item["status"] == "fail" for item in unresolved) else "blocked")
        self.report["finished_at"] = now()
        self.flush()
        return 0 if passed else 1

    def run(self) -> int:
        try:
            self.step("snapshot", self.snapshot)
            self.step("protocol", self.protocol)
            self.step("baseline", checks.baseline, self.root)
            audit = self.step("source_audit", checks.source_audit, self.root)
            self.step("pure_spec_sources", checks.pure_spec_sources, self.root)
            issues = self.step("issues", checks.issue_registry, self.root)
            if issues:
                self.report["issue_inputs"] = issues["input_hashes"]
            specs = self.step("specifications", checks.specifications, self.root)
            roles = self.step("metadata_reviews", metadata.validate, self.root, specs) if specs else None
            if not specs:
                self.skip("metadata_reviews", "Independent paper specifications are not validated")
            coverage = self.step("canonical_coverage", checks.canonical_coverage, self.root, specs) if specs else None
            if not specs:
                self.skip("canonical_coverage", "Independent specifications are absent or invalid")
            claims = coverage["claims"] if coverage else {}
            self.canonical_claims = claims
            if not claims:
                try:
                    from .common import indexed
                    self.canonical_claims = indexed(read_json(self.root / "fidelity/canonical_claims.json").get("claims"), "canonical claims")
                except (EvidenceError, TypeError):
                    self.canonical_claims = {}
            if self.static_only:
                self.report["limitations"].append("Static-only mode never establishes overall or fresh reproduction success")
                for name in ("tools", "dependencies", "build", "fidelity_compile", "environment_export",
                             "environment_validation", "reviews", "exact_experiments", "clean_rebuild", "archive_rebuild",
                             "certificates", "semantic_mutations", "route_dependencies"):
                    self.skip(name, "--static-only: fresh compiled evidence was not produced")
            else:
                available = self.step("tools", self.tools)
                if available:
                    self.step("semantic_mutations", self.compiled_semantic_mutations)
                else:
                    self.skip("semantic_mutations", "Fixed Lean executable unavailable")
                dependencies = self.step("dependencies", self.dependencies) if available else None
                if not available:
                    self.skip("dependencies", "Required build tools unavailable")
                if self.skip_build:
                    self.report["limitations"].append("--skip-build cannot establish fresh kernel compilation or reproduction")
                    self.skip("build", "--skip-build was requested")
                elif available:
                    self.step("build", self.build_math, self.root, "math-build")
                else:
                    self.skip("build", "Required build tools unavailable")
                compiled = self.step("fidelity_compile", self.compile_fidelity, self.root, "fidelity") if available else None
                if not available:
                    self.skip("fidelity_compile", "Required build tools unavailable")
                exported = self.step("environment_export", self.export) if compiled else None
                if not compiled:
                    self.skip("environment_export", "Fidelity modules were not compiled successfully")
                if exported and audit and claims:
                    env = self.step("environment_validation", checks.environment,
                                    read_json(self.folder / "environment.json"), claims,
                                    audit["modules_with_declarations"])
                else:
                    env = None
                    self.skip("environment_validation", "Compiled environment or canonical/source evidence missing")
                if env and exported:
                    self.step("certificates", checks.certificates, self.root, env, claims)
                    self.step("route_dependencies", self.route_check, env, claims)
                    self.step("reviews", self.review_check, claims, env, exported, roles.get("roles", {}) if roles else ())
                else:
                    self.skip("reviews", "Cannot validate reviews against a current complete compiled environment")
                    self.skip("certificates", "Current complete compiled environment unavailable")
                    self.skip("route_dependencies", "Current complete compiled environment unavailable")
                if claims:
                    self.step("exact_experiments", self.exact_experiments, claims)
                else:
                    self.skip("exact_experiments", "Canonical claim coverage is not established")
                if available and dependencies and not self.skip_build:
                    self.step("clean_rebuild", self.reproduce, "clean")
                    # The archive is created independently again; never reuse an
                    # earlier run's unverified archive or status.
                    self.step("archive_rebuild", lambda: self.reproduce("archive", from_archive=True))
                else:
                    for name in ("clean_rebuild", "archive_rebuild"):
                        self.skip(name, "Fresh build disabled or pinned dependency evidence unavailable")
            self.step("source_stability", self.stability)
        except BaseException as exc:
            self.report["steps"]["interrupted"] = {"status": "blocked", "reason": f"{type(exc).__name__}: {exc}"}
            self.report["limitations"].append("Run interrupted; completed evidence remains recoverable")
            self.report["steps"]["source_stability"] = {"status": "blocked", "reason": "Interrupted before final source stability check"}
        return self.finish()

    def protocol(self) -> dict:
        data = read_json(self.root / "fidelity/protocol.json")
        if data.get("schema_version") != 1:
            raise EvidenceError("Unsupported fidelity protocol version")
        if set(data.get("axiom_allowlist", [])) != set(checks.AXIOM_ALLOWLIST):
            raise EvidenceError("Protocol cannot weaken the fixed axiom allowlist")
        return {"schema_version": 1, "sha256": digest(self.root / "fidelity/protocol.json")}
