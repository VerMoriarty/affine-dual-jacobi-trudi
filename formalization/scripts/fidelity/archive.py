"""Portable source inventory plus the checked closure of current evidence.

Unreferenced historical runs/packets and recursive reproduction archives are
not selected. Historical tool-hash inventories are provenance, not requests to
replace current executable sources with an older tool version.
"""
from pathlib import Path
import re
import zipfile

from .common import (EvidenceError, canonical_digest, digest, digest_bytes, input_snapshot, portable_paths, read_json,
                     regular_project_file, require_digest, require_text, tool_snapshot)


def inventory(root: Path) -> dict[str, str]:
    root = root.resolve()
    selected = {**input_snapshot(root), **tool_snapshot(root)}
    queue, visited = [], set()

    def name_for(name):
        path = Path(require_text(name, "archive evidence path"))
        if path.is_absolute():
            if path.is_relative_to(root):
                path = path.relative_to(root)
            elif path.name in {"authoritative.pdf", "authoritative.txt"}:
                path = Path("fidelity/inputs") / path.name
            elif path.parts.count("affine_dual_jt_complete") == 1:
                # Frozen author records retain the original project prefix.
                # Preserve the exact relative identity, then verify its hash;
                # do not rebind arbitrary external files by their basename.
                path = Path(*path.parts[path.parts.index("affine_dual_jt_complete") + 1:])
            else:
                raise EvidenceError(f"External evidence has no portable archive identity: {name}")
        name = path.as_posix()
        if set(path.parts) & {".lake", ".tooling", ".git", "__pycache__"}:
            raise EvidenceError(f"Excluded cache/toolchain cannot be archive evidence: {name}")
        if path.suffix == ".zip" and name != "fidelity/inputs/original-source.zip":
            raise EvidenceError(f"Recursive/archive evidence requires an external delivery bundle: {name}")
        if name.startswith("fidelity/runs/") and path.name.endswith(".raw.json"):
            raise EvidenceError(f"Raw historical export is not portable review evidence: {name}")
        return name

    def add(name, expected=None, *, recurse=False):
        name = name_for(name)
        path = regular_project_file(root, name)
        # Thousands of judgments cite the same large environment. Hash once
        # during collection, then freshly rehash every selected file at exit.
        actual = selected[name] if name in selected else digest(path)
        if expected is not None and actual != require_digest(expected, name):
            raise EvidenceError(f"Stale archive evidence reference: {name}")
        if name in selected and selected[name] != actual:
            raise EvidenceError(f"Archive input changed during selection: {name}")
        selected[name] = actual
        # The protocol contains schema examples, not evidence references.
        # Hash and deliver those bytes, without treating example paths as files.
        if (recurse and path.suffix == ".json" and not name.endswith("fidelity/protocol.json")
                and name not in visited):
            queue.append(name)
        return name

    # Required user-facing instructions and the runnable test/tool suite.
    add("README.md")
    for folder in ("scripts", "tests"):
        for path in sorted((root / folder).rglob("*")):
            if path.is_file() and not set(path.relative_to(root).parts) & {"__pycache__", ".pytest_cache"}:
                add(path.relative_to(root).as_posix())
    for name in (".gitignore", "STATIC_CHECK.json", "lean-toolchain.rc3", "lakefile.rc3.toml"):
        if (root / name).is_file():
            add(name)
    for name in ("fidelity/README.md", "fidelity/REPORT.zh-CN.md", "fidelity/repair_history.json",
                 "fidelity/proof_route.mmd", "fidelity/proof_route_paths.json", "fidelity/lean_release_receipt.json",
                 "fidelity/original_manifest.json", "fidelity/checker_tests.json", "fidelity/checker_tests.log"):
        if (root / name).is_file():
            # Historical manifests retain original file hashes as provenance;
            # they do not require current README/tool bytes to equal history.
            add(name)
    for path in sorted((root / "fidelity/issues").rglob("*")):
        if path.is_file() and path.suffix in {".json", ".md"}:
            add(path.relative_to(root).as_posix(), recurse=path.name == "registry.json")
    for name in ("fidelity/baseline.json", "fidelity/canonical_claims.json", "fidelity/certificates.json",
                 "fidelity/route_requirements.json", "fidelity/original_preservation.json"):
        if (root / name).is_file():
            add(name, recurse=True)
    for path in sorted((root / "fidelity/specs").glob("*.json")):
        add(path.relative_to(root).as_posix(), recurse=True)
    for path in sorted((root / "fidelity/reviews").glob("*.json")):
        add(path.relative_to(root).as_posix(), recurse=True)
        if path.with_suffix(".md").is_file():
            add(path.with_suffix(".md").relative_to(root).as_posix())

    def walk(value, document, blind_manifest=False):
        if isinstance(value, list):
            for item in value:
                walk(item, document, blind_manifest)
        elif isinstance(value, dict):
            # Semantic/route packets retain their source-to-copy identities.
            if "source" in value and "packet" in value and "sha256" in value:
                copied = (Path(document).parent / value["packet"]).as_posix()
                add(copied, value["sha256"], recurse=True)
                add(value["source"], value.get("source_sha256", value["sha256"]), recurse=True)
            if "path" in value and "sha256" in value:
                add(value["path"], value["sha256"], recurse=True)
            for field, child in value.items():
                if field == "bound_input_hashes" and blind_manifest:
                    # A blind packet consumes only allowed_copied_inputs. Its
                    # old whole-project hash inventory was never read input
                    # for the isolated reverse translator.
                    continue
                if field in {"inputs", "bound_input_hashes", "input_hashes"} and isinstance(child, dict):
                    for path, sha in child.items():
                        if isinstance(sha, str):
                            add(path, sha, recurse=True)
                        elif isinstance(sha, dict) and "path" in sha and "sha256" in sha:
                            add(sha["path"], sha["sha256"], recurse=True)
                elif field not in {"bound_tools_hashes", "tools", "tool_hashes"}:
                    walk(child, document, blind_manifest)
    while queue:
        name = queue.pop()
        if name in visited:
            continue
        visited.add(name)
        data = read_json(root / name)
        walk(data, name, data.get("role") == "lean_reverse" and "allowed_copied_inputs" in data)
    portable_paths(list(selected))
    # Final source/evidence stability check closes the selection/read race.
    for name, expected in selected.items():
        if digest(regular_project_file(root, name)) != expected:
            raise EvidenceError(f"Archive evidence changed during closure collection: {name}")
    return dict(sorted(selected.items()))


def completed_run_files(root: Path, run_id: str) -> tuple[dict[str, str], dict]:
    """Bind a completed run and its logs, without recursively bundling ZIPs.

    Reproduction archives are checked against their recorded digests. Their
    inventories and hashes are delivered; the archives themselves stay out of
    the outer archive to prevent recursive delivery growth.
    """
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,95}", run_id):
        raise EvidenceError("Invalid completed evidence run identity")
    root = root.resolve()
    base = f"fidelity/runs/{run_id}"
    report_path = regular_project_file(root, f"{base}/report.json")
    report = read_json(report_path)
    if (report.get("run_id") != run_id or not report.get("finished_at")
            or report.get("overall") not in {"pass", "fail", "blocked"}):
        raise EvidenceError("Evidence run is not completed")
    if report.get("inputs") != input_snapshot(root) or report.get("tools") != tool_snapshot(root):
        raise EvidenceError("Completed evidence run is stale for current inputs or tools")
    if report["overall"] == "pass":
        mandatory = read_json(root / "fidelity/protocol.json").get("mandatory_steps", [])
        if not mandatory or any(report.get("steps", {}).get(step, {}).get("status") != "pass" for step in mandatory):
            raise EvidenceError("Completed pass label omits required successful checks")
    auxiliary = {path.relative_to(root).as_posix(): digest(regular_project_file(root, path.relative_to(root).as_posix()))
                 for folder in ("fidelity/reviews", "fidelity/issues")
                 for path in sorted((root / folder).rglob("*.json"))}
    if report.get("review_and_issue_inputs") != auxiliary:
        raise EvidenceError("Completed evidence run has stale review or issue evidence")
    files = {}
    def add(name, expected=None):
        if not name.startswith(base + "/"):
            raise EvidenceError("Command output escaped its evidence run")
        actual = digest(regular_project_file(root, name))
        if expected is not None and actual != require_digest(expected, name):
            raise EvidenceError("Completed run artifact hash differs: " + name)
        files[name] = actual
    add(f"{base}/report.json")
    add(f"{base}/inputs.json")
    inputs = read_json(root / base / "inputs.json")
    if inputs.get("inputs") != report["inputs"] or inputs.get("snapshot_sha256") != canonical_digest(report["inputs"]):
        raise EvidenceError("Completed run input inventory differs from its report")
    for command in report.get("commands", []):
        if not command.get("finished_at") or command.get("status") == "running":
            raise EvidenceError("Completed report contains an unfinished command")
        if command.get("status") == "pass" and command.get("exit_code") != 0:
            raise EvidenceError("Completed command pass label contradicts its exit code")
        for stream in ("stdout", "stderr"):
            add(command[stream], command[stream + "_sha256"])
        for artifact in command.get("artifacts", []):
            add(artifact["path"], artifact["sha256"])
    export = report.get("steps", {}).get("environment_export", {})
    if export.get("status") == "pass":
        details = export["details"]
        add(details["path"], details["sha256"])
        add(f"{base}/environment.raw.json", details["raw_sha256"])
    for step in ("semantic_mutations", "exact_experiments"):
        record = report.get("steps", {}).get(step, {})
        if record.get("status") == "pass":
            artifact = record.get("details", {}).get("output")
            if not isinstance(artifact, dict):
                raise EvidenceError("Completed run omits output binding: " + step)
            add(artifact["path"], artifact["sha256"])
    omitted = []
    for step, label in (("clean_rebuild", "clean"), ("archive_rebuild", "archive")):
        record = report.get("steps", {}).get(step, {})
        if record.get("status") == "pass":
            name = f"{base}/reproduction-{label}-source.zip"
            actual = digest(regular_project_file(root, name))
            expected = record["details"]["source_archive_sha256"]
            if actual != require_digest(expected, name):
                raise EvidenceError("Completed reproduction archive differs from its report")
            manifest = record["details"].get("source_manifest")
            if not isinstance(manifest, dict) or manifest.get("path") != f"{base}/reproduction-{label}-manifest.json":
                raise EvidenceError("Completed reproduction omits its bound source inventory")
            add(manifest["path"], manifest["sha256"])
            with zipfile.ZipFile(root / name) as archive:
                actual_inventory = {item.filename: digest_bytes(archive.read(item))
                                    for item in archive.infolist() if not item.is_dir()}
            if read_json(root / manifest["path"]) != actual_inventory:
                raise EvidenceError("Reproduction source inventory differs from the verified ZIP")
            omitted.append({"path": name, "sha256": actual,
                            "source_manifest": manifest,
                            "reason": "Source inventory and build logs are included; recursive source ZIP omitted."})
    return files, {"run_id": run_id, "overall": report["overall"],
                   "report_sha256": files[f"{base}/report.json"],
                   "omitted_reproduction_archives": omitted}
