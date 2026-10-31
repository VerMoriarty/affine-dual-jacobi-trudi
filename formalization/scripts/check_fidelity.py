#!/usr/bin/env python3
"""Run the content-bound, fail-closed paper/Lean fidelity audit.

Only a full fresh run can return zero. --static-only and --skip-build always
leave overall acceptance incomplete. Every run gets a new evidence directory;
submitted logs and old success labels are never used as current build evidence.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
import sys
import uuid

from fidelity.common import EvidenceError
from fidelity.runner import Runner


ROOT = Path(__file__).resolve().parents[1]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true", help="audit static inputs; never accept overall fidelity")
    parser.add_argument("--skip-build", action="store_true", help="export with existing math artifacts; never accept fresh reproduction")
    parser.add_argument("--run-id", default=None, help="new, safe evidence directory name (existing names cannot be reused)")
    parser.add_argument("--command-timeout", type=int, default=3600, metavar="SECONDS",
                        help="maximum time per build command (default 3600)")
    args = parser.parse_args(argv)
    if args.command_timeout < 1:
        parser.error("--command-timeout must be positive")
    run_id = args.run_id or (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ-") + uuid.uuid4().hex[:8])
    try:
        runner = Runner(ROOT, run_id, static_only=args.static_only,
                        skip_build=args.skip_build, timeout=args.command_timeout)
    except (EvidenceError, OSError) as exc:
        print(f"Fidelity audit could not start: {exc}", file=sys.stderr)
        return 2
    result = runner.run()
    print(f"Fidelity: {runner.report['overall']}")
    for dimension, status in runner.report["dimensions"].items():
        print(f"  {dimension}: {status}")
    print(f"Report: {runner.folder / 'report.json'}")
    for item in runner.report["unresolved"]:
        print(f"  {item['step']}: {item['status']}: {item['reason']}")
    return result


if __name__ == "__main__":
    raise SystemExit(main())
