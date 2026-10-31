#!/usr/bin/env python3
"""Report syntactic Lean holes without counting comments or string literals.

This is a source audit, not a replacement for Lean's axiom dependency audit.
Run with --write to refresh the checked-in JSON report, or --strict for a failing
exit status when holes, custom axioms, or unsafe declarations remain.
"""

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def code_only(source: str) -> str:
    """Blank comments/strings while preserving offsets and line numbers."""
    out = list(source)
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i:i + 2] = "  "
                i += 2
            else:
                in_string = source[i] != '"'
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            out[i:end] = " " * (end - i)
            i = end
        elif source[i] == '"':
            in_string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def collect() -> dict:
    files = sorted((ROOT / "AffineDualJT").rglob("*.lean"))
    holes = []
    axioms = []
    unsafe = []
    imports = []
    per_module = {}
    line_count = 0
    for path in files:
        source = path.read_text()
        code = code_only(source)
        relative = str(path.relative_to(ROOT))
        line_count += len(source.splitlines())
        matches = list(re.finditer(r"\b(?:sorry|admit)\b", code))
        per_module[relative] = len(matches)
        for match in matches:
            line = source.count("\n", 0, match.start()) + 1
            holes.append({"file": relative, "line": line, "token": match.group()})
        for word, target in [("axiom", axioms), ("unsafe", unsafe)]:
            for match in re.finditer(rf"\b{word}\b", code):
                target.append({"file": relative, "line": source.count("\n", 0, match.start()) + 1})
        for module in re.findall(r"^import\s+(AffineDualJT(?:\.[\w]+)*)", code, re.M):
            if not (ROOT / (module.replace(".", "/") + ".lean")).is_file():
                imports.append({"file": relative, "import": module})
    return {
        "source": "source.tex",
        "audit_kind": "source_only; run Lean Audit.lean for transitive axiom dependencies",
        "modules": len(files),
        "lean_lines": line_count,
        "proof_holes": len(holes),
        "holes_by_module": per_module,
        "holes": holes,
        "custom_axiom_tokens": axioms,
        "unsafe_tokens": unsafe,
        "missing_internal_imports": imports,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--list", action="store_true", help="print every hole")
    args = parser.parse_args()
    report = collect()
    if args.write:
        (ROOT / "STATIC_CHECK.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    if args.list:
        for hole in report["holes"]:
            print(f"{hole['file']}:{hole['line']}: {hole['token']}")
    print(f"{report['modules']} modules; {report['proof_holes']} proof/definition holes; "
          f"{len(report['custom_axiom_tokens'])} custom axiom tokens; "
          f"{len(report['unsafe_tokens'])} unsafe tokens")
    failed = any(report[key] for key in [
        "proof_holes", "custom_axiom_tokens", "unsafe_tokens", "missing_internal_imports"
    ])
    return int(args.strict and failed)


if __name__ == "__main__":
    raise SystemExit(main())
