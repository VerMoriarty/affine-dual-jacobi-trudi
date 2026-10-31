"""Exact experiment output helpers; experiments themselves supply both sides.

An experiment runner imports ``Case`` and ``emit_report`` and accepts an
``--output`` path. This module supplies no successful example or default case.
The checker independently parses and compares every serialized rational.
"""

from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Iterable

from .common import EvidenceError, save_json


def rational(value: int | Fraction) -> str:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise EvidenceError("Exact experiments accept only int or Fraction values")
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


@dataclass
class Case:
    id: str
    claims: list[str]
    details: dict = field(default_factory=dict)
    comparisons: list[dict] = field(default_factory=list)

    def compare(self, left: int | Fraction, right: int | Fraction, label: str = "") -> None:
        self.comparisons.append({"left": rational(left), "right": rational(right), "label": label})

    def to_json(self) -> dict:
        passed = bool(self.comparisons) and all(
            Fraction(item["left"]) == Fraction(item["right"]) for item in self.comparisons)
        return {"id": self.id, "claims": self.claims, "details": self.details,
                "comparisons": self.comparisons, "status": "pass" if passed else "fail"}


def emit_report(path: Path, cases: Iterable[Case], open_issues: list | None = None) -> int:
    entries = [case.to_json() for case in cases]
    issues = [] if open_issues is None else open_issues
    report = {"schema_version": 1, "arithmetic": "exact", "cases": entries, "open_issues": issues}
    save_json(path, report)
    return 0 if entries and not issues and all(item["status"] == "pass" for item in entries) else 1
