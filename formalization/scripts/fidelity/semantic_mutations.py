#!/usr/bin/env python3
"""Compile true Lean theorems expressing wrong targets, then reject them against a fixed spec.

These deliberately bad *statements* have complete rfl/assumption proofs.  A
successful fixture compilation alone must not be mistaken for paper fidelity.
The mutations live only in fresh temporary directories, never in project math.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


FIXTURES = {
    "object_redefined_as_rhs": (
        "def paperObject (n : Nat) := n + 1\n"
        "def implementedObject (n : Nat) := n + 2\n"
        "theorem wrongObject : implementedObject 3 = 5 := rfl\n"
        "#print axioms wrongObject\n",
        "example : paperObject 3 = 4 := wrongObject\n",
    ),
    "goal_added_as_hypothesis": (
        "def paperObject (n : Nat) := n + 1\n"
        "theorem goalAssumed (h : paperObject 3 = 4) : paperObject 3 = 4 := h\n"
        "#print axioms goalAssumed\n",
        "example : paperObject 3 = 4 := goalAssumed\n",
    ),
    "weakened_parameter_scope": (
        "def paperObject (n : Nat) := n + 1\n"
        "theorem onlyWidthOne : paperObject 1 = 2 := rfl\n"
        "#print axioms onlyWidthOne\n",
        "example : forall n : Nat, paperObject n = n + 1 := onlyWidthOne\n",
    ),
}


def evaluate(lean: str, folder: Path) -> dict:
    version = subprocess.run([lean, "--version"], text=True, capture_output=True,
                             timeout=30, check=False)
    if version.returncode:
        raise RuntimeError("Lean version command failed: " + version.stderr)
    cases = []
    for name, (source, certificate) in FIXTURES.items():
        if any(word in source.split() for word in ("sorry", "admit", "axiom", "unsafe")):
            raise RuntimeError("Mutation fixture must have complete proofs and no custom axioms")
        bad = folder / f"{name}.lean"
        bad.write_text(source, encoding="utf-8")
        compiled = subprocess.run([lean, str(bad)], text=True, capture_output=True,
                                  timeout=90, check=False)
        check = folder / f"{name}_certificate.lean"
        check.write_text(source + certificate, encoding="utf-8")
        rejected = subprocess.run([lean, str(check)], text=True, capture_output=True,
                                  timeout=90, check=False)
        diagnostic = rejected.stdout + rejected.stderr
        passed = (compiled.returncode == 0 and rejected.returncode != 0
                  and "type mismatch" in diagnostic.lower()
                  and "does not depend on any axioms" in compiled.stdout
                  and "sorryAx" not in compiled.stdout)
        cases.append({
            "id": name, "status": "pass" if passed else "fail",
            "fixture_source": source, "independent_certificate": certificate,
            "fixture_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "fixture_compilation_exit_code": compiled.returncode,
            "fixture_stdout": compiled.stdout, "fixture_stderr": compiled.stderr,
            "certificate_exit_code": rejected.returncode,
            "certificate_stdout": rejected.stdout, "certificate_stderr": rejected.stderr,
            "claim": "compiled complete wrong-target proof rejected by independently fixed type",
        })
    return {"schema_version": 1, "supporting_only": True,
            "lean_version": version.stdout.strip(), "cases": cases,
            "status": "pass" if all(c["status"] == "pass" for c in cases) else "fail",
            "limitations": "Tests the acceptance boundary; does not prove the paper or semantic correspondence."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        with tempfile.TemporaryDirectory(prefix="fidelity-semantic-mutants-") as temp:
            result = evaluate(args.lean, Path(temp))
    except (OSError, subprocess.SubprocessError, RuntimeError) as exc:
        result = {"schema_version": 1, "status": "blocked", "reason": str(exc), "cases": []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"Compiled semantic mutations: {result['status']} ({len(result['cases'])} cases)")
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
