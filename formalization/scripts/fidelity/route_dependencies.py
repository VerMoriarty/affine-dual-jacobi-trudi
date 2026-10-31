"""Check source-specified checkpoints in the *actual* proof dependency graph."""
from .checks import dependency_closure
from .common import EvidenceError, digest, read_json, regular_project_file, require_list, require_text


def validate(root, env, claims):
    data = read_json(root / "fidelity/route_requirements.json")
    if data.get("schema_version") != 1:
        raise EvidenceError("Unsupported route requirements")
    results = []
    for rule in require_list(data.get("rules"), "route requirements", nonempty=True):
        claim = require_text(rule.get("claim"), "route claim")
        if claim not in claims:
            raise EvidenceError("Unknown route claim: " + claim)
        entry = require_text(rule.get("proof_entrypoint"), "route proof entrypoint")
        if entry not in env or env[entry].get("kind") != "theorem":
            raise EvidenceError("Missing actual proof entrypoint: " + entry)
        required = require_list(rule.get("required_dependencies"), "route checkpoints", nonempty=True)
        if entry in required:
            raise EvidenceError("A proof cannot count itself as a route checkpoint")
        closure = dependency_closure([entry], env) - {entry}
        missing = set(required) - closure
        if missing:
            raise EvidenceError(f"Proof route changed for {claim}: missing {sorted(missing)}")
        for evidence in require_list(rule.get("source_evidence"), "route source evidence", nonempty=True):
            path = regular_project_file(root, evidence["path"])
            if digest(path) != evidence["sha256"]:
                raise EvidenceError("Stale source for route checkpoint")
            require_text(evidence.get("locator"), "route source locator")
        results.append({"claim": claim, "proof_entrypoint": entry,
                        "verified_checkpoints": required, "strict_dependency_count": len(closure)})
    return {"rules": results, "status": "pass"}
