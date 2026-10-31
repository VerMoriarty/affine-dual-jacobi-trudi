"""Independent source-reconciliation and Lean-only reverse-report validation.

These roles establish inspectable input/coverage provenance. Neither role is a
semantic, route, kernel, or reproduction verdict.
"""
from pathlib import Path

from . import checks
from .common import (EvidenceError, canonical_digest, digest, digest_bytes, indexed,
                     read_json, regular_project_file, require_list, require_text)

ROLES = frozenset({"spec_reconciliation", "lean_reverse"})


def _inputs(root, data, label):
    supplied = checks._input_map(data.get("inputs"), label)
    for name, expected in supplied.items():
        checks.source_input(root, name, expected)
    return supplied


def reconciliation(root, data, specs, *, frozen_sha256=checks.FROZEN_CANONICAL_SHA256):
    if data.get("role") != "spec_reconciliation" or data.get("schema_version") != 1:
        raise EvidenceError("Unsupported source reconciliation role")
    supplied = _inputs(root, data, "source reconciliation")
    allowed = {f"fidelity/specs/paper_{side}.{extension}" for side in ("a", "b")
               for extension in ("json", "md")} | {
                   "fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt"}
    if set(supplied) != allowed:
        raise EvidenceError("Reconciliation must bind precisely independent paper specifications and authoritative sources")
    identity = data.get("independent_identity")
    if not isinstance(identity, dict):
        raise EvidenceError("Missing independent reconciliation identity")
    for field in ("task_identity", "role", "method"):
        require_text(identity.get(field), f"reconciliation identity.{field}")
    if data.get("open_issues") != []:
        raise EvidenceError("Source reconciliation contains unresolved issues")
    frozen_path = regular_project_file(root, "fidelity/specs/canonical_math.json")
    if digest(frozen_path) != frozen_sha256:
        raise EvidenceError("Reconciliation's frozen canonical output hash changed")
    frozen = indexed(read_json(frozen_path).get("claims"), "frozen canonical claims")
    alignment = {}
    for item in require_list(data.get("canonical_alignment"), "canonical alignment", nonempty=True):
        key = require_text(item.get("canonical_id"), "alignment canonical_id")
        if key in alignment or key not in frozen:
            raise EvidenceError(f"Duplicate or unknown reconciliation canonical ID: {key}")
        for field in ("kind", "page", "locator", "paper_a", "paper_b", "mapping_relation", "statement", "source_evidence"):
            if item.get(field) != frozen[key].get(field):
                raise EvidenceError(f"Reconciliation differs from frozen mathematics: {key}.{field}")
        checks._evidence(root, item["source_evidence"], f"reconciliation {key}")
        alignment[key] = item
    if set(alignment) != set(frozen):
        raise EvidenceError("Reconciliation canonical alignment is incomplete")
    for side in ("paper_a", "paper_b"):
        references = {ref for item in alignment.values() for ref in item[side]}
        if references != set(specs[side]):
            raise EvidenceError(f"Reconciliation does not cover independent {side} atoms")
        recorded = data.get("validation", {}).get(side, {})
        if recorded.get("atoms") != len(specs[side]) or recorded.get("covered_unique_atoms") != len(references):
            raise EvidenceError(f"Reconciliation records incorrect {side} coverage")
    b_alignment = {}
    for item in require_list(data.get("paper_b_alignment"), "paper_b alignment", nonempty=True):
        key = require_text(item.get("paper_b_id"), "paper_b alignment id")
        if key in b_alignment or key not in specs["paper_b"]:
            raise EvidenceError("Duplicate or unknown paper_b reconciliation atom")
        expected = {claim_id for claim_id, claim in frozen.items() if key in claim["paper_b"]}
        actual = require_list(item.get("canonical_ids"), "paper_b canonical references", nonempty=True)
        if len(actual) != len(set(actual)) or set(actual) != expected:
            raise EvidenceError(f"Incorrect paper_b reverse alignment: {key}")
        b_alignment[key] = item
    if set(b_alignment) != set(specs["paper_b"]):
        raise EvidenceError("Incomplete paper_b reverse alignment")
    for item in require_list(data.get("adjudications"), "reconciliation adjudications"):
        if item.get("status") != "resolved":
            raise EvidenceError("Unresolved source adjudication")
        if any(key not in frozen for key in require_list(item.get("canonical_claims"), "adjudication claims")):
            raise EvidenceError("Unknown source-adjudication claim")
        checks._evidence(root, item.get("source_evidence"), "source adjudication")
    return {"role": "spec_reconciliation", "reviewer": identity["task_identity"],
            "canonical_claims": len(frozen), "paper_a_atoms": len(specs["paper_a"]),
            "paper_b_atoms": len(specs["paper_b"]), "frozen_output_sha256": frozen_sha256}


def lean_reverse(root, data):
    if data.get("role") != "lean_reverse" or data.get("schema_version") != 1:
        raise EvidenceError("Unsupported Lean-only reverse role")
    supplied = _inputs(root, data, "Lean-only reverse report")
    reviewer = data.get("reviewer")
    if not isinstance(reviewer, dict) or reviewer.get("independent") is not True:
        raise EvidenceError("Missing independent Lean-only reverse reviewer identity")
    identity = require_text(reviewer.get("id"), "Lean-only reverse reviewer")
    packet_names = [name for name in supplied if name.endswith("/implementation_environment.json")]
    if len(packet_names) != 1:
        raise EvidenceError("Lean-only reverse report needs exactly one implementation packet")
    packet = read_json(regular_project_file(root, packet_names[0]))
    if not isinstance(packet.get("decls"), list) or not packet["decls"]:
        raise EvidenceError("Missing Lean-only implementation declarations")
    original = [name for name, sha in supplied.items() if name.endswith("/environment.json")
                and sha == packet.get("original_environment_sha256")]
    if len(original) != 1:
        raise EvidenceError("Lean-only packet does not bind its original environment")
    if set(supplied) != {packet_names[0], original[0]}:
        raise EvidenceError("Lean-only reverse inputs escaped the implementation-only role")
    raw = read_json(regular_project_file(root, original[0]))
    implementation = [decl for decl in raw.get("decls", []) if decl.get("module") == "AffineDualJT"
                      or decl.get("module", "").startswith("AffineDualJT.")]
    if implementation != packet["decls"]:
        raise EvidenceError("Lean-only packet differs from original implementation environment")
    env = {decl["name"]: decl for decl in implementation}
    if len(env) != len(implementation):
        raise EvidenceError("Duplicate implementation declaration in Lean-only packet")
    records = {}
    for record in require_list(data.get("declarations"), "reverse declarations", nonempty=True):
        name = require_text(record.get("name"), "reverse declaration name")
        if name in records or name not in env:
            raise EvidenceError("Duplicate or unknown reverse declaration")
        decl = env[name]
        if record.get("full_type") != decl["type"] or record.get("full_type_sha256") != digest_bytes(decl["type"].encode()):
            raise EvidenceError(f"Lean-only reconstructed type differs from export: {name}")
        for field in ("module", "kind", "axioms", "value_available"):
            if record.get(field) != decl.get(field):
                raise EvidenceError(f"Lean-only declaration metadata differs: {name}.{field}")
        for field, exported in (("project_type_dependencies", "type_constants"),
                                ("project_value_dependencies", "value_constants")):
            expected = {ref for ref in decl.get(exported, []) if ref in env}
            if set(require_list(record.get(field), f"{name}.{field}")) != expected:
                raise EvidenceError(f"Lean-only direct dependencies differ: {name}.{field}")
        records[name] = record
    if set(records) != set(env):
        raise EvidenceError("Lean-only reverse declaration coverage is incomplete")
    coverage = data.get("coverage")
    if not isinstance(coverage, dict) or set(coverage.get("all_decl_ids_indexed", [])) != set(env):
        raise EvidenceError("Lean-only coverage inventory differs from implementation")
    for field, ids in coverage.items():
        if isinstance(ids, list) and any(name not in env for name in ids):
            raise EvidenceError(f"Unknown Lean-only coverage reference: {field}")
    modules = data.get("module_index")
    if not isinstance(modules, dict):
        raise EvidenceError("Missing Lean-only module index")
    indexed_names = []
    for module, names in modules.items():
        for name in require_list(names, "reverse module names"):
            if name not in env or env[name]["module"] != module:
                raise EvidenceError("Incorrect Lean-only module index")
            indexed_names.append(name)
    if len(indexed_names) != len(set(indexed_names)) or set(indexed_names) != set(env):
        raise EvidenceError("Incomplete or duplicate Lean-only module index")
    for obj in require_list(data.get("objects"), "reverse objects"):
        name = obj.get("name")
        if name not in env or obj.get("actual_definition") != env[name].get("definition"):
            raise EvidenceError("Reverse object definition differs from implementation")
        body = obj.get("actual_definition")
        expected_hash = digest_bytes(body.encode()) if isinstance(body, str) else None
        if body is not None and not isinstance(body, str):
            raise EvidenceError("Malformed reverse object definition")
        if obj.get("definition_sha256") != expected_hash:
            raise EvidenceError("Reverse object definition digest differs")
    for item in require_list(data.get("inspected_inputs"), "Lean-only inspected inputs", nonempty=True):
        name = require_text(item.get("path"), "inspected path")
        if item.get("read") is not True or not name.startswith(str(Path(packet_names[0]).parent) + "/"):
            raise EvidenceError("Lean-only reviewer inspection escaped its isolated packet")
        checks.source_input(root, name, item.get("sha256"))
    return {"role": "lean_reverse", "reviewer": identity, "declarations": len(records),
            "implementation_sha256": canonical_digest(implementation), "semantic_verdict": "not provided by this role"}


def validate(root: Path, specs: dict) -> dict:
    found = {}
    for path in sorted((root / "fidelity/reviews").glob("*.json")):
        data = read_json(path)
        role = data.get("role")
        if role not in ROLES:
            continue
        if role in found:
            raise EvidenceError(f"Duplicate metadata reviewer role: {role}")
        result = reconciliation(root, data, specs) if role == "spec_reconciliation" else lean_reverse(root, data)
        found[role] = {**result, "path": path.relative_to(root).as_posix(), "sha256": digest(path)}
    missing = ROLES - set(found)
    if missing:
        raise EvidenceError(f"Missing independent metadata reviews: {sorted(missing)}")
    return {"roles": found}
