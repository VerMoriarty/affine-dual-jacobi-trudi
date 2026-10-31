"""Pure validators. No validator infers success from a submitted PASS label."""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from pathlib import Path
import re

from .common import (AXIOM_ALLOWLIST, DIMENSIONS, EvidenceError, code_only,
                     canonical_digest, digest, indexed, mathematical_sources, read_json,
                     regular_project_file, require_digest, require_list,
                     require_text)


BASELINE_FILES = {
    "authoritative_pdf": ("fidelity/inputs/authoritative.pdf",),
    "source_tex": ("source.tex", "fidelity/inputs/reference.tex"),
    "packaged_pdf": ("source.pdf", "fidelity/inputs/packaged.pdf"),
    "lean_toolchain": ("lean-toolchain",),
    "lakefile": ("lakefile.toml",),
    "lake_manifest": ("lake-manifest.json",),
    "source_archive": ("fidelity/inputs/original-source.zip",),
}

FROZEN_CANONICAL_SHA256 = "a4c231b77eb70d75157c9855cb13fe5e6f97f1716fdc68dc8bcf89069ff3f414"
REQUIRED_CONTAINERS = frozenset({"A", "B", "L2.1", "P2.2", "T3.1", "L3.2", "L3.3",
                                "P4.1", "P4.2", "P5.1", "L5.2", "P5.3", "L5.4", "P5.5", "P6.1", "C6.2"})
PURE_SPEC_MODULES = frozenset({"FidelityLean.Spec", "FidelityLean.ZeroParameterSpec"})


def source_input(root: Path, name: str, expected: str) -> Path:
    """Resolve a recorded source without silently rebinding arbitrary paths.

    Only a missing absolute authoritative.pdf/txt path has a portable alias.
    Existing absolute paths must match their own digest; there is no fallback
    from stale existing evidence to a convenient copy.
    """
    path = Path(name)
    if not path.is_absolute():
        path = regular_project_file(root, name)
    elif not path.exists():
        if path.name not in {"authoritative.pdf", "authoritative.txt"}:
            raise EvidenceError(f"Missing source input with no portable alias: {name}")
        candidates = list((root / "fidelity/inputs").rglob(path.name))
        if len(candidates) != 1 or candidates[0] != root / "fidelity/inputs" / path.name:
            raise EvidenceError(f"Missing or ambiguous portable source alias: {name}")
        path = regular_project_file(root, f"fidelity/inputs/{path.name}")
    if not path.is_file() or digest(path) != expected:
        raise EvidenceError(f"Stale source input: {name}")
    return path


def baseline(root: Path) -> dict:
    data = read_json(root / "fidelity/baseline.json")
    if data.get("schema_version") != 1 or data.get("authority") != "authoritative_pdf":
        raise EvidenceError("Unsupported or ambiguous authoritative baseline")
    inputs = data.get("inputs")
    if not isinstance(inputs, dict):
        raise EvidenceError("Baseline inputs must be an object")
    verified = {}
    for key, aliases in BASELINE_FILES.items():
        item = inputs.get(key)
        if not isinstance(item, dict):
            raise EvidenceError(f"Missing pinned baseline input: {key}")
        expected = require_digest(item.get("sha256"), key)
        for name in aliases:
            actual = digest(regular_project_file(root, name))
            if actual != expected:
                raise EvidenceError(f"Stale or mutated baseline input: {name}")
            verified[name] = actual
    archive = inputs["source_archive"]
    name = require_text(archive.get("path"), "source_archive.path")
    # The portable provenance ZIP is mandatory and relative paths resolve
    # against the project root, regardless of the invoking working directory.
    path = Path(name) if Path(name).is_absolute() else regular_project_file(root, name)
    if not path.is_file() or digest(path) != archive["sha256"]:
        raise EvidenceError("Missing or stale pinned source archive")
    return {"verified_inputs": verified, "source_archive_present": True,
            "source_archive_path": name}


def source_audit(root: Path) -> dict:
    findings = []
    modules = []
    declaration_modules = []
    for path in mathematical_sources(root):
        relative = path.relative_to(root).as_posix()
        module = relative[:-5].replace("/", ".")
        modules.append(module)
        source = path.read_text(encoding="utf-8")
        code = code_only(source)
        for match in re.finditer(
                r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|"
                r"Lean\.ofReduceBool|Lean\.trustCompiler)\b", code):
            findings.append({"path": relative, "line": code.count("\n", 0, match.start()) + 1,
                             "token": match.group()})
        if re.search(r"\b(?:theorem|lemma|def|abbrev|inductive|structure|class|instance)\b", code):
            declaration_modules.append(module)
        for imported in re.findall(r"^\s*import\s+((?:AffineDualJT|FidelityLean)(?:\.[\w]+)*)", code, re.M):
            if imported == "FidelityLean.Export":
                findings.append({"path": relative, "forbidden_tool_import": imported})
            if not (root / (imported.replace(".", "/") + ".lean")).is_file():
                findings.append({"path": relative, "missing_import": imported})
    if findings:
        raise EvidenceError(f"Source audit rejected {findings}")
    return {"modules": modules, "modules_with_declarations": declaration_modules,
            "axiom_allowlist": sorted(AXIOM_ALLOWLIST), "findings": findings}


def pure_spec_sources(root: Path) -> dict:
    files = {"FidelityLean/Spec.lean": ["Mathlib"]}
    extension = root / "FidelityLean/ZeroParameterSpec.lean"
    if extension.exists():
        files["FidelityLean/ZeroParameterSpec.lean"] = ["FidelityLean.Spec"]
    result = {}
    for name, allowed in files.items():
        code = code_only(regular_project_file(root, name).read_text(encoding="utf-8"))
        imports = []
        for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M):
            imports.extend(line.split())
        if imports != allowed:
            raise EvidenceError(f"Independent specification import firewall failed: {name}: {imports}")
        result[name] = {"imports": imports, "sha256": digest(root / name)}
    return result


def pure_spec_environment(env: dict) -> dict:
    checked = []
    for name, item in env.items():
        if item.get("module") not in PURE_SPEC_MODULES:
            continue
        for ref in (*item.get("type_constants", []), *item.get("value_constants", [])):
            origin = env.get(ref, {}).get("module", "")
            if (ref.startswith(("AffineDualJT.", "Fidelity.Bridge", "Fidelity.Certificate"))
                    or origin == "AffineDualJT" or origin.startswith("AffineDualJT.")
                    or (origin.startswith("FidelityLean.") and origin not in PURE_SPEC_MODULES)):
                raise EvidenceError(f"Independent specification depends on implementation/bridge/certificate: {name} -> {ref}")
        checked.append(name)
    return {"checked_declarations": len(checked), "modules": sorted(PURE_SPEC_MODULES)}


def _input_map(value: object, label: str) -> dict[str, str]:
    if isinstance(value, list):
        result = {}
        for item in value:
            if not isinstance(item, dict):
                raise EvidenceError(f"Malformed {label} input entry")
            name = require_text(item.get("path"), f"{label}.path")
            if name in result:
                raise EvidenceError(f"Duplicate {label} input path: {name}")
            result[name] = require_digest(item.get("sha256"), name)
        return result
    if isinstance(value, dict) and value:
        return {require_text(name, label): require_digest(sha, name)
                for name, sha in value.items()}
    raise EvidenceError(f"Missing or malformed {label} input hashes")


def specifications(root: Path) -> dict:
    result = {}
    for side in ("paper_a", "paper_b"):
        path = root / f"fidelity/specs/{side}.json"
        data = read_json(path)
        if data.get("schema_version") != 1 or data.get("role") != f"paper_spec_{side[-1]}":
            raise EvidenceError(f"Unsupported independent specification: {side}")
        supplied = _input_map(data.get("inputs"), side)
        for name, expected in supplied.items():
            try:
                source_input(root, name, expected)
            except EvidenceError as exc:
                raise EvidenceError(f"Stale {side} source input: {name}: {exc}") from exc
        # Each independent extraction must actually bind the authoritative PDF
        # or its recorded extracted text, never only the packaged manuscript.
        authority = {digest(regular_project_file(root, name)) for name in
                     ("fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt")}
        if not authority.intersection(supplied.values()):
            raise EvidenceError(f"{side} does not bind an authoritative paper input")
        atoms = indexed(data.get("claims"), f"{side}.claims")
        for key, atom in atoms.items():
            if atom.get("kind") not in {"definition", "convention", "statement", "proof_step"}:
                raise EvidenceError(f"Unknown atomic kind: {side}:{key}")
            for field in ("container", "locator", "statement"):
                require_text(atom.get(field), f"{side}:{key}.{field}")
            if atom.get("page") in (None, "", []):
                raise EvidenceError(f"Missing paper page: {side}:{key}")
            for field in ("assumptions", "objects", "route", "edge_cases"):
                require_list(atom.get(field), f"{side}:{key}.{field}")
        result[side] = atoms
    return result


def canonical_coverage(root: Path, specs: dict, *,
                       frozen_sha256: str = FROZEN_CANONICAL_SHA256) -> dict:
    data = read_json(root / "fidelity/canonical_claims.json")
    if data.get("schema_version") != 1:
        raise EvidenceError("Unsupported canonical claims schema")
    claims = indexed(data.get("claims"), "canonical claims")
    frozen_path = root / "fidelity/specs/canonical_math.json"
    if frozen_path.is_file():
        if digest(frozen_path) != frozen_sha256:
            raise EvidenceError("Frozen independent canonical mathematics hash changed")
        frozen = indexed(read_json(frozen_path).get("claims"), "frozen canonical claims")
        if set(frozen) != set(claims):
            raise EvidenceError("Canonical claim IDs differ from frozen independent mathematics")
        for key, claim in claims.items():
            actual = {field: value for field, value in claim.items() if field != "declarations"}
            expected = {field: value for field, value in frozen[key].items() if field != "declarations"}
            if actual != expected:
                changed = sorted(field for field in set(actual) | set(expected)
                                 if actual.get(field) != expected.get(field) or (field in actual) != (field in expected))
                raise EvidenceError(f"Frozen independent canonical mathematics changed: {key}: {changed}")
    coverage = {}
    for key, claim in claims.items():
        relation = claim.get("mapping_relation")
        if relation not in {"equivalent", "component_of", "source_only"}:
            raise EvidenceError(f"Missing or unsupported mapping_relation: {key}")
        sides = {}
        for side in ("paper_a", "paper_b"):
            refs = require_list(claim.get(side), f"{key}.{side}")
            refs = [require_text(ref, f"{key}.{side} atom") for ref in refs]
            if len(refs) != len(set(refs)):
                raise EvidenceError(f"Duplicate atom within canonical claim: {key}.{side}")
            sides[side] = refs
        if not sides["paper_a"] and not sides["paper_b"]:
            raise EvidenceError(f"Canonical claim has no source atoms: {key}")
        if (not sides["paper_a"] or not sides["paper_b"]) and relation != "source_only":
            raise EvidenceError(f"An empty mapping side requires source_only: {key}")
        sources = _evidence(root, claim.get("source_evidence"), f"canonical source {key}")
        paper_sources = {"fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt",
                         "fidelity/inputs/reference.tex", "source.tex"}
        if not sources.intersection(paper_sources):
            raise EvidenceError(f"Canonical mapping lacks direct original-paper evidence: {key}")
    for side in ("paper_a", "paper_b"):
        uses = Counter()
        for key, claim in claims.items():
            refs = claim[side]
            for ref in refs:
                uses[ref] += 1
        unknown = sorted(set(uses) - set(specs[side]))
        missing = sorted(set(specs[side]) - set(uses))
        reused = sorted(key for key, count in uses.items() if count > 1)
        coverage[side] = {"atoms": len(specs[side]), "covered": len(uses),
                          "reference_count": sum(uses.values()),
                          "unknown": unknown, "missing": missing, "reused_atoms": reused}
        if unknown or missing:
            raise EvidenceError(f"Atomic coverage is incomplete or unknown for {side}: {coverage[side]}")
    for key, claim in claims.items():
        declarations = require_list(claim.get("declarations"), f"{key}.declarations", nonempty=True)
        if len(set(declarations)) != len(declarations):
            raise EvidenceError(f"Duplicate declarations for {key}")
        for name in declarations:
            require_text(name, f"{key}.declaration")
        if claim.get("open_issues", []) != []:
            raise EvidenceError(f"Unresolved canonical issues: {key}")
    if data.get("open_issues", []) != []:
        raise EvidenceError("Canonical claims contain unresolved issues")
    return {"claims": claims, "coverage": coverage}


def environment(data: dict, claims: dict, declaration_modules: list[str]) -> dict:
    """Validate every exported declaration, not merely named headline theorems."""
    decls = data.get("decls")
    if not isinstance(decls, list) or not decls:
        raise EvidenceError("Missing compiled environment declarations")
    result = {}
    for declaration in decls:
        if not isinstance(declaration, dict):
            raise EvidenceError("Malformed compiled declaration")
        name = require_text(declaration.get("name"), "declaration.name")
        if name in result:
            raise EvidenceError(f"Duplicate exported declaration: {name}")
        require_text(declaration.get("module"), f"{name}.module")
        if declaration["module"] == "FidelityLean.Export":
            raise EvidenceError("Executable exporter tooling must not enter the mathematical environment")
        type_text = require_text(declaration.get("type"), f"{name}.type")
        type_hash = require_digest(declaration.get("type_hash"), f"{name}.type_hash")
        # The serialized type hash is independently recomputed by Python.
        from .common import digest_bytes
        if digest_bytes(type_text.encode("utf-8")) != type_hash:
            raise EvidenceError(f"Exported type hash does not match its text: {name}")
        for field in ("type_constants", "value_constants", "axioms"):
            values = require_list(declaration.get(field), f"{name}.{field}")
            for constant in values:
                require_text(constant, f"{name}.{field}")
            if len(values) != len(set(values)):
                raise EvidenceError(f"Duplicate dependency in {name}.{field}")
        forbidden = set(declaration["axioms"]) - AXIOM_ALLOWLIST
        if forbidden:
            raise EvidenceError(f"Forbidden transitive axioms in {name}: {sorted(forbidden)}")
        if name in {"sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"}:
            raise EvidenceError(f"Untrusted declaration in export: {name}")
        result[name] = declaration
    actual_modules = {decl["module"] for decl in result.values()}
    missing_modules = sorted(set(declaration_modules) - actual_modules)
    if missing_modules:
        raise EvidenceError(f"Environment omits mathematical modules: {missing_modules}")
    for claim_id, claim in claims.items():
        missing = set(claim["declarations"]) - set(result)
        if missing:
            raise EvidenceError(f"Compiled environment misses {claim_id}: {sorted(missing)}")
    # Any project constant named by a dependency must have its own exported
    # record; omitting an inconvenient intermediary must not hide its axioms.
    for name, declaration in result.items():
        missing = {constant for field in ("type_constants", "value_constants")
                   for constant in declaration[field]
                   if constant.startswith(("AffineDualJT.", "Fidelity.", "FidelityLean.",
                                           "_private.AffineDualJT.", "_private.FidelityLean."))
                   and constant not in result}
        if missing:
            raise EvidenceError(f"Environment has a truncated project closure at {name}: {sorted(missing)}")
    pure_spec_environment(result)
    return result


def certificates(root: Path, env: dict, claims: dict, *,
                 required_containers: frozenset[str] = REQUIRED_CONTAINERS) -> dict:
    data = read_json(root / "fidelity/certificates.json")
    if data.get("schema_version") != 1:
        raise EvidenceError("Unsupported independent certificate manifest")
    entries = indexed(data.get("entries"), "certificate entries")
    covered, per_claim = set(), {key: [] for key in claims}
    results = []
    for key, entry in entries.items():
        container = require_text(entry.get("container"), f"{key}.container")
        if container not in required_containers:
            raise EvidenceError(f"Unknown certificate source container: {container}")
        specification = require_text(entry.get("specification"), f"{key}.specification")
        certificate = require_text(entry.get("certificate"), f"{key}.certificate")
        spec, proof = env.get(specification), env.get(certificate)
        if not spec or spec.get("module") not in PURE_SPEC_MODULES or not specification.startswith("Fidelity.Spec."):
            raise EvidenceError(f"Missing independently defined specification: {specification}")
        if not proof or proof.get("kind") != "theorem" or not certificate.startswith("Fidelity.Certificate."):
            raise EvidenceError(f"Missing compiled theorem certificate: {certificate}")
        if specification not in proof.get("type_constants", []):
            raise EvidenceError(f"Certificate type omits its independent specification: {certificate}")
        refs = require_list(entry.get("claims"), f"{key}.claims", nonempty=True)
        if len(set(refs)) != len(refs):
            raise EvidenceError(f"Duplicate certificate claim references: {key}")
        for ref in refs:
            if ref not in claims:
                raise EvidenceError(f"Unknown canonical certificate claim: {ref}")
            if claims[ref].get("container") != container:
                raise EvidenceError(f"Certificate container differs from canonical claim: {key}:{ref}")
            per_claim[ref].append(certificate)
        covered.add(container)
        results.append({"id": key, "container": container, "specification": specification,
                        "certificate": certificate, "claims": refs})
    missing = required_containers - covered
    if missing:
        raise EvidenceError(f"Missing independent certificate source containers: {sorted(missing)}")
    pure_spec_environment(env)
    return {"entries": results, "containers": sorted(covered), "per_claim": per_claim,
            "manifest_sha256": digest(root / "fidelity/certificates.json")}


def semantic_mutations(root: Path, output: dict) -> dict:
    from .semantic_mutations import FIXTURES
    pin = regular_project_file(root, "lean-toolchain").read_text().strip()
    version = re.search(r"Lean \(version ([^,\s)]+)", require_text(output.get("lean_version"), "mutation Lean version"))
    if not version or version.group(1) != pin.removeprefix("leanprover/lean4:v"):
        raise EvidenceError("Compiled semantic mutations used a different Lean version")
    if output.get("schema_version") != 1 or output.get("supporting_only") is not True:
        raise EvidenceError("Unsupported compiled semantic mutation evidence")
    cases = indexed(output.get("cases"), "compiled semantic mutation cases")
    if set(cases) != set(FIXTURES):
        raise EvidenceError("Missing or unknown compiled semantic mutation cases")
    for key, case in cases.items():
        source, certificate = FIXTURES[key]
        if case.get("fixture_source") != source or case.get("independent_certificate") != certificate:
            raise EvidenceError(f"Compiled mutation fixture/certificate changed: {key}")
        from .common import digest_bytes
        if case.get("fixture_sha256") != digest_bytes(source.encode()):
            raise EvidenceError(f"Compiled mutation fixture hash differs: {key}")
        compiled, rejected = case.get("fixture_compilation_exit_code"), case.get("certificate_exit_code")
        if type(compiled) is not int or compiled != 0 or type(rejected) is not int or rejected <= 0:
            raise EvidenceError(f"Compiled mutation requires a successful proof and rejected fixed type: {key}")
        stdout = require_text(case.get("fixture_stdout"), f"{key}.fixture_stdout")
        theorem = re.search(r"#print axioms\s+(\w+)", source).group(1)
        if (not re.search(r"['`]?" + re.escape(theorem) + r"['`]? does not depend on any axioms", stdout)
                or any(word in stdout for word in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"))):
            raise EvidenceError(f"Compiled wrong-target fixture lacks no-axiom evidence: {key}")
        diagnostic = require_text(case.get("certificate_stdout", "") + case.get("certificate_stderr", ""), f"{key}.certificate_diagnostic")
        if "type mismatch" not in diagnostic.lower():
            raise EvidenceError(f"Mutation rejection did not diagnose a type mismatch: {key}")
        if case.get("status") != "pass":
            raise EvidenceError(f"Compiled semantic mutation is unresolved: {key}")
    if output.get("status") != "pass":
        raise EvidenceError("Compiled semantic mutation run is unresolved")
    return {"cases": len(cases), "lean_version": output["lean_version"], "supporting_only": True}


def dependency_closure(declarations: list[str], env: dict) -> set[str]:
    seen, pending = set(), list(declarations)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        item = env.get(name)
        if item:
            pending.extend(item["type_constants"])
            pending.extend(item["value_constants"])
    return seen


def _evidence(root: Path, evidence: object, label: str, hashes: dict | None = None) -> set[str]:
    sources = set()
    for item in require_list(evidence, f"{label}.evidence", nonempty=True):
        if not isinstance(item, dict):
            raise EvidenceError(f"Malformed evidence for {label}")
        name = require_text(item.get("path"), f"{label}.evidence.path")
        expected = require_digest(item.get("sha256"), name)
        require_text(item.get("locator"), f"{label}.evidence.locator")
        path = regular_project_file(root, name)
        actual = hashes.get(name) if hashes is not None else None
        if actual is None:
            actual = digest(path)
            if hashes is not None:
                hashes[name] = actual
        if actual != expected:
            raise EvidenceError(f"Stale evidence for {label}: {name}")
        sources.add(name)
    return sources


def _judgment(root: Path, judgment: object, label: str, hashes: dict | None = None) -> set[str]:
    if not isinstance(judgment, dict):
        raise EvidenceError(f"Missing review dimension: {label}")
    if judgment.get("status") != "pass":
        raise EvidenceError(f"Unresolved or rejected review dimension: {label}: {judgment.get('status')}")
    require_text(judgment.get("rationale"), f"{label}.rationale")
    return _evidence(root, judgment.get("evidence"), label, hashes)


def issue_registry(root: Path) -> dict:
    """Check current issue state while preserving historical open findings.

    Every ID in a raw issue report must have a current registry entry. A
    resolved label alone is insufficient: referenced evidence must exist
    and match its recorded digest.
    """
    registry_path = root / "fidelity/issues/registry.json"
    data = read_json(registry_path)
    if data.get("schema_version") != 1:
        raise EvidenceError("Unsupported current issue registry schema")
    entries = require_list(data.get("issues"), "current issue registry")
    issues = {}
    for item in entries:
        if not isinstance(item, dict):
            raise EvidenceError("Malformed current issue registry entry")
        key = require_text(item.get("id"), "issue.id")
        if key in issues:
            raise EvidenceError(f"Duplicate current issue registry ID: {key}")
        issues[key] = item
    discovered, reports = set(), {}
    def collect_ids(value):
        if isinstance(value, dict):
            for field in ("id", "issue_id"):
                if isinstance(value.get(field), str) and value[field]:
                    discovered.add(value[field])
            for child in value.values():
                collect_ids(child)
        elif isinstance(value, list):
            for child in value:
                collect_ids(child)
    for path in sorted((root / "fidelity/issues").rglob("*.json")):
        if path == registry_path:
            continue
        name = path.relative_to(root).as_posix()
        regular_project_file(root, name)
        collect_ids(read_json(path))
        reports[name] = digest(path)
    missing = discovered - set(issues)
    if missing:
        raise EvidenceError(f"Discovered issues omitted from current registry: {sorted(missing)}")
    for key, item in issues.items():
        if item.get("status") != "resolved":
            raise EvidenceError(f"Unresolved current issue: {key}: {item.get('status')}")
        _evidence(root, item.get("evidence"), f"resolved issue {key}")
    reports["fidelity/issues/registry.json"] = digest(registry_path)
    return {"current_issues": len(issues), "discovered_ids": sorted(discovered),
            "resolved_ids": sorted(issues), "input_hashes": reports}


def reviews(root: Path, inputs: dict, claims: dict, env: dict,
            environment_content_sha256: str, *, validated_metadata_roles=(),
            claim_evidence: dict | None = None) -> dict:
    paths = sorted((root / "fidelity/reviews").glob("*.json"))
    if not paths:
        raise EvidenceError("Missing independent semantic and route reviews")
    semantic, route, identities, errors = [], [], {}, []
    evidence_hashes = {}
    evidence = {key: {**{dimension: [] for dimension in DIMENSIONS}, "route": []} for key in claims}
    def judge(root, judgment, label):
        try:
            return _judgment(root, judgment, label, evidence_hashes), None
        except (EvidenceError, TypeError, KeyError) as exc:
            return set(), str(exc)
    def remember(key, dimension, identity, path, judgment, error):
        evidence[key][dimension].append({"reviewer": identity,
            "review": path.relative_to(root).as_posix(), "status": "pass" if error is None else "fail",
            "reason": error, "evidence": judgment.get("evidence", []) if isinstance(judgment, dict) else []})
    for path in paths:
        try:
            data = read_json(path)
            if data.get("schema_version") != 1:
                raise EvidenceError(f"Unsupported review schema: {path.name}")
            role = data.get("role")
            if role in {"spec_reconciliation", "lean_reverse"}:
                if role not in validated_metadata_roles:
                    raise EvidenceError(f"Metadata role requires its independent validator: {role}")
                continue
            if role not in {None, "semantic", "semantic_1", "semantic_2", "route"}:
                raise EvidenceError(f"Unknown review role: {path.name}: {role}")
            kind = data.get("kind")
            if kind not in {"semantic", "route"}:
                raise EvidenceError(f"Unknown review kind: {path.name}")
            if (role == "route" and kind != "route") or (role in {"semantic", "semantic_1", "semantic_2"} and kind != "semantic"):
                raise EvidenceError(f"Review role/kind mismatch: {path.name}")
            reviewer = data.get("reviewer")
            if not isinstance(reviewer, dict) or reviewer.get("independent") is not True:
                raise EvidenceError(f"Missing independent reviewer identity: {path.name}")
            identity = require_text(reviewer.get("id"), "reviewer.id")
            if data.get("open_issues") != []:
                raise EvidenceError(f"Unresolved or undeclared review issues: {path.name}")
            supplied = _input_map(data.get("inputs"), path.name)
            for name, expected in inputs.items():
                if supplied.get(name) != expected:
                    raise EvidenceError(f"Stale or missing review input in {path.name}: {name}")
            for name, expected in supplied.items():
                if digest(regular_project_file(root, name)) != expected:
                    raise EvidenceError(f"Stale review evidence in {path.name}: {name}")
            environments = [read_json(regular_project_file(root, name)) for name in supplied
                            if name.endswith("/environment.json")]
            if not any(canonical_digest(item.get("decls")) == environment_content_sha256 for item in environments):
                raise EvidenceError(f"Review does not bind current compiled environment: {path.name}")
            from .inspection import validate as validate_inspection
            inspection = validate_inspection(root, data, kind, supplied)
            judgments = indexed(data.get("claims"), f"review {path.name}")
            if set(judgments) != set(claims):
                errors.append(f"Review claim coverage differs from canonical claims: {path.name}")
        except (EvidenceError, TypeError, KeyError) as exc:
            errors.append(str(exc))
            continue
        for key, item in judgments.items():
            if key not in claims:
                continue
            if item.get("open_issues", []) != []:
                errors.append(f"Open review issues for {path.name}:{key}")
                continue
            if kind == "semantic":
                dimensions = item.get("dimensions")
                if not isinstance(dimensions, dict) or set(dimensions) != set(DIMENSIONS):
                    errors.append(f"Expected all five semantic dimensions: {path.name}:{key}")
                    dimensions = dimensions if isinstance(dimensions, dict) else {}
                sources = set()
                for dimension in DIMENSIONS:
                    judgment = dimensions.get(dimension)
                    used, error = judge(root, judgment, f"{path.name}:{key}:{dimension}")
                    sources.update(used)
                    remember(key, dimension, identity, path, judgment, error)
                    if error:
                        errors.append(error)
                if not any(name.startswith("fidelity/specs/") for name in sources):
                    errors.append(f"Semantic review lacks paper specification evidence: {key}")
                    for dimension in DIMENSIONS:
                        evidence[key][dimension][-1].update(status="fail", reason="Missing paper specification evidence")
                if not any(name.endswith("/environment.json") for name in sources):
                    errors.append(f"Semantic review lacks compiled type evidence: {key}")
                    for dimension in DIMENSIONS:
                        evidence[key][dimension][-1].update(status="fail", reason="Missing compiled type evidence")
            else:
                judgment = item.get("route")
                _, error = judge(root, judgment, f"{path.name}:{key}:route")
                try:
                    anchors = require_list(item.get("dependency_anchors"), f"{key}.dependency_anchors", nonempty=True)
                    closure = dependency_closure(claims[key]["declarations"], env)
                    if any(not isinstance(anchor, str) or anchor not in closure for anchor in anchors):
                        raise EvidenceError(f"Route anchors are absent from actual dependency closure: {key}")
                except (EvidenceError, TypeError, KeyError) as exc:
                    error = str(exc)
                remember(key, "route", identity, path, judgment, error)
                if error:
                    errors.append(error)
        record = {"path": path.relative_to(root).as_posix(), "reviewer": identity,
                  "sha256": digest(path), "claims": len(judgments), "inspection": inspection}
        (semantic if kind == "semantic" else route).append(record)
        identities[path.name] = identity
    if len({item["reviewer"] for item in semantic}) < 2:
        errors.append("Two distinct independent semantic reviewers are required")
    if not route:
        errors.append("Missing independent proof-route review")
    changed = set()
    for name, expected in evidence_hashes.items():
        try:
            if digest(regular_project_file(root, name)) != expected:
                changed.add(name)
        except EvidenceError:
            changed.add(name)
    if changed:
        errors.append(f"Evidence changed during review validation: {sorted(changed)}")
        for dimensions in evidence.values():
            for records in dimensions.values():
                for record in records:
                    if any(item.get("path") in changed for item in record["evidence"]):
                        record.update(status="fail", reason="Evidence changed during review validation")
    per_claim = {}
    for key, dimensions in evidence.items():
        per_claim[key] = {}
        for dimension, records in dimensions.items():
            needed = 1 if dimension == "route" else 2
            accepted = {record["reviewer"] for record in records if record["status"] == "pass"}
            rejected = any(record["status"] == "fail" for record in records)
            status = "fail" if rejected else ("pass" if len(accepted) >= needed else "blocked")
            per_claim[key][dimension] = {"status": status, "reviews": records,
                                         "accepted_reviewers": sorted(accepted), "required_reviewers": needed}
    if claim_evidence is not None:
        claim_evidence.clear()
        claim_evidence.update(per_claim)
    if errors:
        raise EvidenceError("; ".join(errors))
    return {"semantic": semantic, "route": route, "identities": identities, "per_claim": per_claim}


def experiments(root: Path, output: dict, claims: dict) -> dict:
    manifest = read_json(root / "fidelity/experiments.json")
    if manifest.get("schema_version") != 1:
        raise EvidenceError("Unsupported exact-experiment manifest")
    required = require_list(manifest.get("required_cases"), "required experiment cases", nonempty=True)
    if any(not isinstance(item, str) or not item for item in required) or len(set(required)) != len(required):
        raise EvidenceError("Malformed or duplicate required experiment cases")
    if output.get("schema_version") != 1 or output.get("arithmetic") != "exact":
        raise EvidenceError("Experiments must declare exact arithmetic schema")
    if output.get("open_issues") != []:
        raise EvidenceError("Unresolved or undeclared exact-experiment issues")
    cases = indexed(output.get("cases"), "experiment cases")
    if set(cases) != set(required):
        raise EvidenceError("Exact-experiment cases do not match the required manifest")
    comparisons = 0
    detected_mutations = 0
    for key, case in cases.items():
        refs = require_list(case.get("claims"), f"{key}.claims", nonempty=True)
        if any(ref not in claims for ref in refs):
            raise EvidenceError(f"Unknown canonical claim in exact experiment: {key}")
        for comparison in require_list(case.get("comparisons"), f"{key}.comparisons", nonempty=True):
            if not isinstance(comparison, dict):
                raise EvidenceError(f"Malformed exact comparison: {key}")
            left, right = comparison.get("left"), comparison.get("right")
            rational = re.compile(r"^-?\d+(?:/[1-9]\d*)?$")
            if not all(isinstance(value, str) and rational.fullmatch(value) for value in (left, right)):
                raise EvidenceError(f"Non-exact rational comparison: {key}")
            if Fraction(left) != Fraction(right):
                raise EvidenceError(f"Exact experiment disagrees: {key}: {left} != {right}")
            comparisons += 1
        if case.get("status") != "pass":
            raise EvidenceError(f"Experiment has unresolved status: {key}")
        if key.startswith(("mutation-", "counterexample-")):
            details = case.get("details")
            if (not isinstance(details, dict) or details.get("expected_counterexample") is not True
                    or details.get("evidence_role") != "supporting_only"):
                raise EvidenceError(f"Missing exact detector evidence: {key}")
            values = [details.get(field) for field in
                      ("correct", "mutant", "difference", "independent_detector_value")]
            if not all(isinstance(value, str) and rational.fullmatch(value) for value in values):
                raise EvidenceError(f"Non-exact mutation detector evidence: {key}")
            correct, mutant, difference, independent = map(Fraction, values)
            if correct != independent or mutant == correct or difference != mutant - correct:
                raise EvidenceError(f"Contradictory exact mutation detector evidence: {key}")
            require_text(details.get("independent_detector_path"), f"{key}.independent_detector_path")
            detected_mutations += 1
    return {"cases": len(cases), "exact_comparisons": comparisons,
            "independently_detected_mutations": detected_mutations,
            "manifest_sha256": digest(root / "fidelity/experiments.json")}
