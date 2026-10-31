#!/usr/bin/env python3
"""Package the source delivery and SHA-256 checksums using only Python's stdlib.

This command does not run Lean or certify that verification has passed.
"""

import argparse
import hashlib
import json
import sys
import tempfile
import zipfile
from pathlib import Path
from fidelity.archive import inventory as archive_inventory, completed_run_files

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_ROOT = "affine_dual_jt_complete"
def delivery_files() -> list[Path]:
    """The same checked evidence closure used by independent rebuilds."""
    return [ROOT / name for name in archive_inventory(ROOT)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=ROOT / "dist" / f"{ARCHIVE_ROOT}-source.zip",
        help="ZIP destination; replace existing archive/checksum files",
    )
    parser.add_argument("--evidence-run", action="append", default=[], metavar="RUN_ID",
                        help="include one completed, current audit run and its checked command logs")
    args = parser.parse_args()
    output = args.output.absolute()
    checksum = output.with_name(output.name + ".sha256")
    if output.suffix.lower() != ".zip":
        parser.error("--output must end in .zip")
    try:
        selected = archive_inventory(ROOT)
        receipts = []
        for run_id in args.evidence_run:
            artifacts, receipt = completed_run_files(ROOT, run_id)
            selected.update(artifacts)
            receipts.append(receipt)
        paths = [ROOT / name for name in sorted(selected)]
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=".package-", dir=output.parent) as temporary:
            staged_output = Path(temporary) / output.name
            staged_checksum = Path(temporary) / checksum.name
            manifest = []
            with zipfile.ZipFile(staged_output, "x", compression=zipfile.ZIP_DEFLATED) as archive:
                for path in paths:
                    relative = path.relative_to(ROOT).as_posix()
                    data = path.read_bytes()
                    if hashlib.sha256(data).hexdigest() != selected[relative]:
                        raise ValueError("Source changed while packaging: " + relative)
                    info = zipfile.ZipInfo(f"{ARCHIVE_ROOT}/{relative}", (1980, 1, 1, 0, 0, 0))
                    info.external_attr = 0o100644 << 16
                    archive.writestr(info, data, compress_type=zipfile.ZIP_DEFLATED)
                    manifest.append(f"{hashlib.sha256(data).hexdigest()}  {relative}\n")
                receipt_data = (json.dumps({"schema_version": 1, "completed_runs": receipts},
                                           ensure_ascii=False, indent=2) + "\n").encode()
                archive.writestr(f"{ARCHIVE_ROOT}/DELIVERY_RUNS.json", receipt_data)
                manifest.append(f"{hashlib.sha256(receipt_data).hexdigest()}  DELIVERY_RUNS.json\n")
                archive.writestr(f"{ARCHIVE_ROOT}/DELIVERY_MANIFEST.sha256", "".join(manifest))
            for relative, expected in selected.items():
                if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                    raise ValueError("Source changed before package completion: " + relative)
            digest = hashlib.sha256(staged_output.read_bytes()).hexdigest()
            staged_checksum.write_text(
                f"{digest}  {output.name}\n", encoding="utf-8",
            )
            staged_output.replace(output)
            staged_checksum.replace(checksum)
    except (OSError, ValueError) as error:
        print(f"Delivery packaging failed: {error}", file=sys.stderr)
        return 1
    print(f"ZIP: {output}")
    print(f"SHA-256: {checksum}")
    print(f"Packaged {len(paths)} files plus delivery receipts and manifest; .lake/ excluded.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
