"""Check fresh-context/inspection attestations without claiming authentication."""
from pathlib import Path

from .common import (EvidenceError, digest, read_json, regular_project_file,
                     require_digest, require_list, require_text)

REQUIRED_SOURCES = frozenset({"fidelity/inputs/authoritative.txt", "fidelity/specs/paper_a.json",
    "fidelity/specs/paper_b.json", "fidelity/specs/canonical_math.json", "fidelity/canonical_claims.json",
    "fidelity/protocol.json", "fidelity/reviews/lean_reverse.json", "fidelity/certificates.json",
    "fidelity/specs/zero_parameter_addendum.json"})


def validate(root, data, kind, supplied):
    reviewer = data.get("reviewer")
    if not isinstance(reviewer, dict) or reviewer.get("fresh_context") is not True:
        raise EvidenceError("Missing fresh_context reviewer attestation")
    reference = data.get("packet_manifest")
    if not isinstance(reference, dict):
        raise EvidenceError("Missing reviewed packet manifest identity")
    name = require_text(reference.get("path"), "packet_manifest.path")
    if not name.startswith("fidelity/packets/") or Path(name).name != "manifest.json":
        raise EvidenceError("Review manifest must identify an isolated review packet")
    path = regular_project_file(root, name)
    if digest(path) != require_digest(reference.get("sha256"), "packet manifest"):
        raise EvidenceError("Stale reviewed packet manifest")
    manifest = read_json(path)
    roles = {"semantic_1", "semantic_2"} if kind == "semantic" else {"route"}
    if (manifest.get("schema_version") != 1 or manifest.get("role") not in roles
            or manifest.get("fresh_context_required") is not True or manifest.get("verdict_created") is not False):
        raise EvidenceError("Reviewed packet role or fresh-context boundary differs")
    from .checks import _input_map
    bound = _input_map(manifest.get("bound_input_hashes"), "packet bound inputs")
    for source, expected in bound.items():
        if supplied.get(source) != expected or digest(regular_project_file(root, source)) != expected:
            raise EvidenceError(f"Stale or missing packet-bound review input: {source}")
    packet = path.parent.relative_to(root)
    copied = {}
    for item in require_list(manifest.get("allowed_copied_inputs"), "packet copied inputs", nonempty=True):
        source = require_text(item.get("source"), "packet source")
        relative = require_text(item.get("packet"), "packet copied path")
        if Path(relative).is_absolute() or ".." in Path(relative).parts:
            raise EvidenceError("Packet copy escaped its isolated folder")
        if source.startswith("fidelity/reviews/") and source not in {
                "fidelity/reviews/lean_reverse.json", "fidelity/reviews/lean_reverse.md"}:
            raise EvidenceError("Reviewer packet contains another semantic verdict")
        if source in copied or item.get("transformation") is not None:
            raise EvidenceError("Duplicate or transformed semantic/route packet input")
        expected = require_digest(item.get("sha256"), source)
        target = (packet / relative).as_posix()
        if bound.get(source) != expected or digest(regular_project_file(root, target)) != expected:
            raise EvidenceError(f"Stale copied review input: {source}")
        copied[source] = target
    environments = [source for source, target in copied.items() if Path(target).name == "environment.json"]
    if len(environments) != 1:
        raise EvidenceError("Review packet needs exactly one compiled environment copy")
    required = set(REQUIRED_SOURCES) | {environments[0]}
    if not required.issubset(copied) or set(manifest.get("required_inspected_sources", [])) != required:
        raise EvidenceError("Review packet omits required independent evidence")
    allowed = set(copied.values()) | {name, (packet / "PROMPT.txt").as_posix()}
    inspected = set()
    for item in require_list(data.get("inspected_inputs"), "review inspected inputs", nonempty=True):
        target = require_text(item.get("path"), "inspected input path")
        if target not in allowed or target in inspected or item.get("read") is not True:
            raise EvidenceError("Review inspection escaped its packet, was duplicated, or was not attested")
        if digest(regular_project_file(root, target)) != require_digest(item.get("sha256"), target):
            raise EvidenceError(f"Stale review inspection evidence: {target}")
        inspected.add(target)
    expected_inspections = {name} | {copied[source] for source in required}
    if not expected_inspections.issubset(inspected):
        raise EvidenceError("Review lacks inspections of required packet evidence")
    return {"packet_manifest": name, "inspected_files": len(inspected), "fresh_context_attested": True,
            "identity_authenticated": False,
            "trust_boundary": "Hashes verify recorded files and role isolation; identity, new context and actual understanding remain reviewer attestations."}
