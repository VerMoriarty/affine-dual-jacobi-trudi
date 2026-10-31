"""Small, dependency-free primitives shared by the fidelity checker and tests."""

from __future__ import annotations

import hashlib
import json
import re
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


AXIOM_ALLOWLIST = frozenset({"propext", "Classical.choice", "Quot.sound"})
DIMENSIONS = ("objects", "statement", "hypotheses", "conclusion", "nonvacuity")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
EXCLUDED = {".git", ".lake", ".tooling", "__pycache__", ".pytest_cache"}


class EvidenceError(ValueError):
    """An absent, malformed, stale, or contradictory evidence artifact."""


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def canonical_digest(value: Any) -> str:
    return digest_bytes(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                   ensure_ascii=False).encode("utf-8"))


def _unique_object(pairs: list[tuple[str, Any]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path) -> dict:
    if not path.is_file():
        raise EvidenceError(f"Missing evidence: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"),
                           object_pairs_hook=_unique_object,
                           parse_constant=lambda value: (_ for _ in ()).throw(
                               EvidenceError(f"Invalid JSON constant: {value}")))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise EvidenceError(f"Cannot read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise EvidenceError(f"Expected JSON object: {path}")
    return value


def save_json(path: Path, value: Any) -> None:
    """Replace a report atomically, so an interrupted run remains inspectable."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False,
                                    sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def regular_project_file(root: Path, name: str) -> Path:
    if not isinstance(name, str) or not name:
        raise EvidenceError("Evidence path must be a nonempty string")
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        raise EvidenceError(f"Expected project-relative path: {name}")
    path = root / relative
    if any((root / parent).is_symlink() for parent in (relative, *relative.parents)):
        raise EvidenceError(f"Symlink is not evidence: {name}")
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise EvidenceError(f"Missing regular project file: {name}")
    return path


def require_digest(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SHA256.fullmatch(value):
        raise EvidenceError(f"Invalid SHA-256 for {label}")
    return value


def require_list(value: Any, label: str, *, nonempty: bool = False) -> list:
    if not isinstance(value, list) or (nonempty and not value):
        raise EvidenceError(f"Expected {'nonempty ' if nonempty else ''}list: {label}")
    return value


def require_text(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise EvidenceError(f"Expected nonempty text: {label}")
    return value


def indexed(items: Any, label: str) -> dict[str, dict]:
    result = {}
    for item in require_list(items, label, nonempty=True):
        if not isinstance(item, dict):
            raise EvidenceError(f"Expected object in {label}")
        key = require_text(item.get("id"), f"{label}.id")
        if key in result:
            raise EvidenceError(f"Duplicate {label} id: {key}")
        result[key] = item
    return result


def code_only(source: str) -> str:
    """Blank nested Lean comments and strings, preserving offsets and newlines.

    This lexical audit is an additional guard; exported kernel dependencies are
    authoritative for axioms. Quoted identifiers are left intact conservatively.
    """
    out = list(source)
    position, depth, in_string = 0, 0, False
    while position < len(source):
        pair = source[position:position + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out[position:position + 2] = "  "
                position += 2
            elif pair == "-/":
                depth -= 1
                out[position:position + 2] = "  "
                position += 2
            else:
                if source[position] != "\n":
                    out[position] = " "
                position += 1
        elif in_string:
            if source[position] == "\\" and position + 1 < len(source):
                if source[position + 1] != "\n":
                    out[position:position + 2] = "  "
                else:
                    out[position] = " "
                position += 2
            else:
                in_string = source[position] != '"'
                if source[position] != "\n":
                    out[position] = " "
                position += 1
        elif pair == "/-":
            depth = 1
            out[position:position + 2] = "  "
            position += 2
        elif pair == "--":
            end = source.find("\n", position)
            end = len(source) if end < 0 else end
            out[position:end] = " " * (end - position)
            position = end
        elif source[position] == '"':
            in_string = True
            out[position] = " "
            position += 1
        else:
            position += 1
    if depth or in_string:
        raise EvidenceError("Unclosed Lean comment or string")
    return "".join(out)


def mathematical_sources(root: Path) -> list[Path]:
    result = sorted((root / "AffineDualJT").rglob("*.lean"))
    entry = root / "AffineDualJT.lean"
    if not result or not entry.is_file():
        raise EvidenceError("Missing AffineDualJT root or mathematical modules")
    # The exporter is executable tooling; its runtime implementation is hashed
    # separately and is never treated as a mathematical certificate.
    fidelity_math = [path for path in sorted((root / "FidelityLean").rglob("*.lean"))
                     if path.name != "Export.lean"]
    return [entry, *result, *fidelity_math]


def portable_paths(names: list[str]) -> None:
    """Reject ZIP inventories that alias on case-insensitive/NFC volumes."""
    seen = {}
    for name in names:
        key = unicodedata.normalize("NFC", name).casefold()
        if key in seen and seen[key] != name:
            raise EvidenceError(f"Casefold/Unicode path collision: {seen[key]} and {name}")
        seen[key] = name


def input_snapshot(root: Path) -> dict[str, str]:
    """Bind all math, specifications, canonical claims, baselines, and locks.

    Reviews and generated runs are deliberately excluded to avoid circular
    digests. Tool source has its own independent digest inventory.
    """
    paths = set(mathematical_sources(root))
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json",
                 "source.tex", "source.pdf", "fidelity/baseline.json",
                 "fidelity/canonical_claims.json", "fidelity/experiments.json",
                 "fidelity/certificates.json", "fidelity/route_requirements.json"):
        if (root / name).is_file():
            paths.add(root / name)
    for folder in ("fidelity/specs", "fidelity/inputs"):
        paths.update(path for path in (root / folder).rglob("*") if path.is_file())
    result = {}
    for path in sorted(paths):
        name = path.relative_to(root).as_posix()
        result[name] = digest(regular_project_file(root, name))
    return result


def tool_snapshot(root: Path) -> dict[str, str]:
    paths = {root / "scripts/check_fidelity.py", root / "fidelity/protocol.json"}
    paths.add(root / "FidelityLean/Export.lean")
    paths.update((root / "scripts/fidelity").rglob("*.py"))
    return {path.relative_to(root).as_posix(): digest(path)
            for path in sorted(paths) if path.is_file()}
