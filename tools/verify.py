#!/usr/bin/env python3
"""Check the source view, then run the unchanged checker in the complete release."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import stat
import subprocess
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARCHIVES = {
    "affine-dual-jt-fidelity-20261031.zip": "0a40289c30aa7fbabf19b8c08b567948f1c94ee93982acea939892912d5823dd",
    "affine-dual-jt-fidelity-verification-20261031.zip": "06e62ccd4320c5be9e130c81d250ac33dbac261391678a04a2eaf62522be5216",
}
PROJECT_NAME = "affine_dual_jt_complete"
WORK = ROOT / "build/verification"
PROJECT = WORK / PROJECT_NAME


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_sources() -> dict:
    for name, expected in ARCHIVES.items():
        path = ROOT / "artifacts" / name
        require(path.is_file(), f"Missing release archive: {path}")
        require(digest(path) == expected, f"Release archive hash differs: {name}")
    manifest = json.loads((ROOT / "docs/source-view-manifest.json").read_text())
    require(manifest["schema_version"] == 1, "Unsupported source-view manifest")
    require(manifest["archive"] == "artifacts/affine-dual-jt-fidelity-20261031.zip", "Source archive changed")
    require(manifest["archive_sha256"] == ARCHIVES["affine-dual-jt-fidelity-20261031.zip"], "Manifest archive hash changed")
    require(manifest["view_root"] == "formalization" and manifest["original_root"] == PROJECT_NAME, "Source roots changed")
    expected_files = manifest["files"]
    actual_files = {
        path.relative_to(ROOT / "formalization").as_posix()
        for path in (ROOT / "formalization").rglob("*") if path.is_file()
        and not any(part in {".lake", "__pycache__", ".git"} for part in path.relative_to(ROOT / "formalization").parts)
    }
    require(actual_files == set(expected_files), "Browsable source inventory differs from the frozen projection")
    with zipfile.ZipFile(ROOT / manifest["archive"]) as archive:
        archive_files = {
            item.filename.removeprefix(PROJECT_NAME + "/") for item in archive.infolist() if not item.is_dir()
        }
        require(archive_files == set(expected_files) | set(manifest["omitted_paths"]), "Projection and omitted inventory do not cover the release")
        require(not (set(expected_files) & set(manifest["omitted_paths"])), "Projection inventory overlaps omitted files")
        for name, entry in expected_files.items():
            require(not Path(name).is_absolute() and ".." not in Path(name).parts, "Invalid projection path")
            path = ROOT / "formalization" / name
            require(not path.is_symlink(), f"Projection is a symlink: {name}")
            require(path.stat().st_size == entry["bytes"] and digest(path) == entry["sha256"], f"Browsable source changed: {name}")
            require(hashlib.sha256(archive.read(PROJECT_NAME + "/" + name)).hexdigest() == entry["sha256"], f"Projection no longer matches frozen archive: {name}")
    return {"archive_hashes": "pass", "source_view": "pass", "view_files": len(expected_files)}


def verify_delivery_manifest(project: Path) -> int:
    # Reused workspaces must not be able to redefine the expected source bytes
    # by editing their own delivery manifest together with a checker script.
    with zipfile.ZipFile(ROOT / "artifacts/affine-dual-jt-fidelity-20261031.zip") as archive:
        frozen_manifest = archive.read(PROJECT_NAME + "/DELIVERY_MANIFEST.sha256")
    require((project / "DELIVERY_MANIFEST.sha256").read_bytes() == frozen_manifest,
            "Extracted delivery manifest differs from the fixed release archive")
    checked = 0
    for line in frozen_manifest.decode("utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, "Malformed frozen delivery manifest")
        expected, name = match.groups()
        require(not Path(name).is_absolute() and ".." not in Path(name).parts, "Invalid delivery manifest path")
        path = project / name
        require(path.is_file() and not path.is_symlink(), f"Missing release evidence: {name}")
        require(digest(path) == expected, f"Extracted release file changed: {name}")
        checked += 1
    require(checked == 457, f"Unexpected frozen manifest size: {checked}")
    return checked


def prepare() -> dict:
    marker = WORK / "prepared.json"
    expected = ARCHIVES["affine-dual-jt-fidelity-20261031.zip"]
    if marker.is_file():
        require(json.loads(marker.read_text())["source_archive_sha256"] == expected, "Prepared source version differs")
        count = verify_delivery_manifest(PROJECT)
        return {"prepared": "reused", "delivery_manifest_files": count, "project": str(PROJECT)}
    require(not PROJECT.exists(), f"Unmarked work directory already exists: {PROJECT}")
    WORK.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(ROOT / "artifacts/affine-dual-jt-fidelity-20261031.zip") as archive:
        for item in archive.infolist():
            parts = Path(item.filename).parts
            require(bool(parts) and parts[0] == PROJECT_NAME and ".." not in parts and not Path(item.filename).is_absolute(), "Unsafe release archive path")
            require(not stat.S_ISLNK(item.external_attr >> 16), "Release archive contains a symlink")
        require(archive.testzip() is None, "Release ZIP CRC check failed")
        archive.extractall(WORK)
    count = verify_delivery_manifest(PROJECT)
    marker.write_text(json.dumps({"source_archive_sha256": expected, "delivery_manifest_files": count}, indent=2) + "\n")
    return {"prepared": "new", "delivery_manifest_files": count, "project": str(PROJECT)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check-only", action="store_true", help="Check archive and browsable-source bytes; no Lean claim")
    mode.add_argument("--prepare-only", action="store_true", help="Check and extract/reuse the complete frozen source; do not run Lean")
    parser.add_argument("--run-id", help="Optional fresh run name for the original checker")
    args = parser.parse_args()
    result = check_sources()
    if args.check_only:
        print(json.dumps({**result, "mode": "bytes_only", "lean_checked": False}), flush=True)
        return 0
    result.update(prepare())
    print(json.dumps(result), flush=True)
    if args.prepare_only:
        print("Prepared the complete release. Lean has not been checked by this preparation step.", flush=True)
        return 0
    command = [sys.executable, "scripts/check_fidelity.py"]
    if args.run_id:
        command.extend(["--run-id", args.run_id])
    # Preserve the original verifier and its exit code. It validates the pinned
    # toolchain/dependencies and builds FidelityLean as well as the main library.
    return subprocess.run(command, cwd=PROJECT, check=False).returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError, zipfile.BadZipFile) as error:
        print(f"Release verification failed: {error}", file=sys.stderr)
        sys.exit(1)
