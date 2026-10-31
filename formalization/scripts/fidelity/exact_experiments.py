#!/usr/bin/env python3
"""Independent, supporting-only exact checks of the paper's seven identities.

The Weyl evaluator implements (2.1) directly.  The affine evaluator separately
constructs (1.1), the row kernels, and (1.2).  Neither imports project mathematics.
Only the standard library is used.  See fidelity/experiment_design.md.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction as Q
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[2]
KINDS = ("C0", "Ct", "BC", "B0", "Bminus", "Bplus", "Bt")
SQUARE_ROOT_KINDS = {"BC", "Bminus"}
SEEDS = ((Q(2), Q(3), Q(5)), (Q(-2), Q(3), Q(-5)))
SOURCE_ANCHORS = {
    "C0": "Theorem A (1.6); (1.1)-(1.2); (2.1), C0 row",
    "Ct": "Theorem A (1.7); (1.1)-(1.2); (2.1), Ct row; Proposition 5.1",
    "BC": "Theorem A (1.8); (1.1)-(1.2); (2.1), BC row",
    "B0": "Theorem A (1.3); (1.1)-(1.2); (2.1), B0 row",
    "Bminus": "Theorem A (1.4); (1.1)-(1.2); (2.1), B-minus row",
    "Bplus": "Theorem A (1.5), positive width; (2.1), B-plus row",
    "Bt": "Theorem B (1.9), positive width; (2.1), Bt row",
    "width_zero": "Section 6.1, Proposition 6.1; Theorems A and B endpoints",
    "Ct_zero": "Section 6.2, final paragraph, and Proposition 5.1 parity projection",
    "domain": "Equation (2.1) displayed denominators and Section 6.1 cancellation convention",
    "faults": "(1.3)-(1.9), zero extension (1.1), and Section 6.1",
}


class DomainError(ValueError):
    """The displayed numerical Weyl formula has a zero denominator."""


def fraction_string(value: int | Q) -> str:
    if isinstance(value, bool) or not isinstance(value, (int, Q)):
        raise TypeError("Only integers and Fraction values are evidence")
    return str(Q(value))


def input_hashes() -> dict[str, str]:
    return {name: sha256((ROOT / name).read_bytes()).hexdigest() for name in (
        "fidelity/inputs/authoritative.pdf", "fidelity/inputs/authoritative.txt")}


def parameter_values(kind: str) -> tuple[Q, ...]:
    return (Q(0), Q(2, 3), Q(-2, 3)) if kind in SQUARE_ROOT_KINDS else (
        Q(0), Q(1), Q(2, 3), Q(-2, 3))


def parameter_tag(q: Q) -> str:
    return fraction_string(q).replace("-", "m").replace("/", "d")


def orbit(seed: tuple[Q, ...]) -> tuple[tuple[Q, ...], ...]:
    """Every signed permutation, including every independent inversion."""
    return tuple(tuple(z if sign == 1 else 1 / z for z, sign in zip(p, signs))
                 for p in permutations(seed) for signs in product((1, -1), repeat=len(seed)))


# LEFT PATH: the complete Weyl-group sum (2.1), without determinant formulas,
# elementary coefficients, row kernels, affine weights, or affine exponents.
def weyl_sum(kind: str, n: int, k: int, parameter: Q, x: tuple[Q, ...],
             *, pair_parameter: Q | None = None, boundary_parameter: Q | None = None) -> Q:
    if kind not in KINDS or n < 1 or k < 0 or len(x) != n:
        raise ValueError("Invalid type, rank, width, or number of variables")
    if any(z == 0 for z in x):
        raise DomainError("inversion requires nonzero variables")
    t = parameter * parameter if kind in SQUARE_ROOT_KINDS else parameter
    if pair_parameter is not None:
        t = pair_parameter
    tau = parameter if boundary_parameter is None else boundary_parameter
    symmetric_normalization = Q(1)
    for r in range(1, n + 1):
        symmetric_normalization *= sum((t ** a for a in range(r)), Q(0))
    if symmetric_normalization == 0:
        raise DomainError("V_n(t) is zero in the displayed Weyl formula")
    boundary_normalization = Q(1)
    if k == 0:
        for r in range(1, n + 1):
            if kind in ("Ct", "Bt"):
                boundary_normalization *= 1 + t ** r
            elif kind == "Bminus":
                boundary_normalization *= 1 - tau ** (2 * r - 1)
            elif kind == "Bplus":
                boundary_normalization *= 1 + t ** (r - 1)
    if boundary_normalization == 0:
        raise DomainError("nu_star(0) is zero in the displayed Weyl formula")
    total = Q(0)
    # Iteration is over all n! 2^n group elements even when a term is cached.
    for p in permutations(x):
        for eta in product((1, -1), repeat=n):
            u = tuple(z if sign == 1 else 1 / z for z, sign in zip(p, eta))
            total += _weyl_term(kind, k, t, tau, u)
    return total / (symmetric_normalization * boundary_normalization)


@lru_cache(maxsize=None)
def _weyl_term(kind: str, k: int, t: Q, tau: Q, u: tuple[Q, ...]) -> Q:
    """Cache repeated *scalar summands*, never a reduced sign-only sum."""
    term = Q(1)
    for z in u:
        if kind in ("C0", "Ct", "BC"):
            denominator = 1 - z * z
            if denominator == 0:
                raise DomainError("1-z^2 is zero")
            numerator = (1 - t * z * z) if kind == "Ct" else (
                (1 + tau * z) if kind == "BC" else Q(1))
            rho = numerator / denominator
        elif kind in ("B0", "Bminus", "Bt"):
            denominator = 1 - z
            if denominator == 0:
                raise DomainError("1-z is zero")
            numerator = (1 + tau * z) if kind == "Bminus" else (
                (1 - t * z) if kind == "Bt" else Q(1))
            rho = numerator / denominator
        else:
            rho = Q(1)
        term *= z ** (-k) * rho
    for a in range(len(u)):
        for b in range(a + 1, len(u)):
            denominator = (u[a] - u[b]) * (1 - u[a] * u[b])
            if denominator == 0:
                raise DomainError("a pair denominator is zero")
            term *= (t * u[a] - u[b]) * (1 - t * u[a] * u[b]) / denominator
    return term


# RIGHT PATH: independent generating polynomial, zero-extended coefficients,
# row support and weights.  It does not use rho, V_n, nu, or Weyl summands.
def generating_coefficients(x: tuple[Q, ...], extra_one: bool = False) -> tuple[Q, ...]:
    coefficients = [Q(1)]
    factors = [z for a in x for z in (a, 1 / a)]
    if extra_one:
        factors.append(Q(1))
    for z in factors:
        updated = [Q(0)] * (len(coefficients) + 1)
        for r, value in enumerate(coefficients):
            updated[r] += value
            updated[r + 1] += z * value
        coefficients = updated
    return tuple(coefficients)


def extended(coefficients: tuple[Q, ...], r: int) -> Q:
    return coefficients[r] if 0 <= r < len(coefficients) else Q(0)


def affine_period(kind: str, k: int) -> int:
    return 2 * k + (2 if kind == "C0" else 1 if kind in ("BC", "B0") else 0)


def kernel_delta(kind: str) -> int:
    return 0 if kind in ("C0", "Ct", "BC") else 2 if kind == "Bplus" else 1


def row_kernel(kind: str, n: int, i: int, m: int, coefficients: tuple[Q, ...]) -> Q:
    first = extended(coefficients, n - i + m)
    second = extended(coefficients, n + i + m - kernel_delta(kind))
    return first - second if kind in ("C0", "Ct", "BC") else first + second


def support_bounds(kind: str, n: int, k: int, i: int) -> tuple[int, int]:
    """Lemma 3.3: ceil((n-i+1-N)/K) <= y <= floor((n+i+k-delta)/K).

    For y below the lower endpoint every index exceeds N. For y above
    the upper endpoint every index is negative.  No empirical cutoff occurs.
    """
    if k == 0:
        raise ValueError("There is no row or period at width zero")
    period = affine_period(kind, k)
    degree = 2 * n + (1 if kind == "Bt" else 0)
    numerator = n - i + 1 - degree
    lower = -((-numerator) // period)
    upper = (n + i + k - kernel_delta(kind)) // period
    return lower, upper


def affine_weight(kind: str, k: int, j: int, y: int, parameter: Q) -> Q:
    # Each branch transcribes its own displayed identity.  There is no shared
    # exponent routine with the Weyl implementation (which has no such weight).
    if kind == "B0":
        twice = (2 * k + 1) * y * y - (2 * j - 1) * y
        assert twice % 2 == 0
        exponent = twice // 2
        sign = -1 if y % 2 else 1
    elif kind == "Bminus":
        exponent = 2 * k * y * y - (2 * j - 1) * y
        sign = 1
    elif kind in ("Bplus", "Bt"):
        exponent = k * y * y - (j - 1) * y
        sign = -1 if y % 2 else 1
    elif kind == "C0":
        exponent = (k + 1) * y * y - j * y
        sign = 1
    elif kind == "Ct":
        exponent = k * y * y - j * y
        sign = 1
    elif kind == "BC":
        exponent = (2 * k + 1) * y * y - 2 * j * y
        sign = -1 if y % 2 else 1
    else:
        raise ValueError(kind)
    assert exponent >= 0, (kind, k, j, y, exponent)
    return sign * parameter ** exponent


def determinant_elimination(matrix: list[list[Q]]) -> Q:
    """Exact row elimination; empty determinant is one."""
    if not matrix:
        return Q(1)
    a = [list(row) for row in matrix]
    answer = Q(1)
    for col in range(len(a)):
        pivot_row = next((r for r in range(col, len(a)) if a[r][col]), None)
        if pivot_row is None:
            return Q(0)
        if pivot_row != col:
            a[col], a[pivot_row] = a[pivot_row], a[col]
            answer = -answer
        pivot = a[col][col]
        answer *= pivot
        for r in range(col + 1, len(a)):
            ratio = a[r][col] / pivot
            for c in range(col + 1, len(a)):
                a[r][c] -= ratio * a[col][c]
            a[r][col] = Q(0)
    return answer


def determinant_leibniz(matrix: list[list[Q]]) -> Q:
    """Independent permutation expansion used for the explicit lattice sum."""
    size = len(matrix)
    answer = Q(0)
    for p in permutations(range(size)):
        inversions = sum(p[i] > p[j] for i in range(size) for j in range(i + 1, size))
        term = Q(-1 if inversions % 2 else 1)
        for i in range(size):
            term *= matrix[i][p[i]]
        answer += term
    return answer


def affine_evaluations(kind: str, n: int, k: int, parameter: Q,
                       x: tuple[Q, ...]) -> tuple[Q, Q, dict]:
    if k == 0:
        # In particular Bplus/Bt do not evaluate a weight, kernel, or half-factor.
        return Q(1), Q(1), {"endpoint": "normalized empty rectangle", "rows_evaluated": 0}
    coefficients = generating_coefficients(x, kind == "Bt")
    period = affine_period(kind, k)
    ranges = [range(lo, hi + 1) for lo, hi in
              (support_bounds(kind, n, k, i) for i in range(1, k + 1))]
    rows: list[dict[int, list[Q]]] = []
    matrix = []
    signed_matrix = []
    for i, ys in enumerate(ranges, start=1):
        row_terms = {y: [affine_weight(kind, k, j, y, parameter) *
                         row_kernel(kind, n, i, j - period * y, coefficients)
                         for j in range(1, k + 1)] for y in ys}
        rows.append(row_terms)
        matrix.append([sum((row_terms[y][j] for y in ys), Q(0)) for j in range(k)])
        signed_matrix.append([sum(((-1 if y % 2 else 1) * row_terms[y][j]
                                    for y in ys), Q(0)) for j in range(k)])
    full = determinant_elimination(matrix)
    if kind == "Ct":
        # Independent parity projector, not replacement by the full lattice.
        via_rows = (full + determinant_elimination(signed_matrix)) / 2
    else:
        via_rows = full / (2 if kind in ("Bplus", "Bt") else 1)
    lattice_total = Q(0)
    terms_visited = 0
    terms_selected = 0
    for y_vector in product(*ranges):
        terms_visited += 1
        if kind == "Ct" and sum(y_vector) % 2:
            continue
        terms_selected += 1
        lattice_total += determinant_leibniz([rows[i][y] for i, y in enumerate(y_vector)])
    via_grid = lattice_total / (2 if kind in ("Bplus", "Bt") else 1)
    return via_rows, via_grid, {
        "row_bounds": [[ys.start, ys.stop - 1] for ys in ranges],
        "lattice_vectors_visited": terms_visited,
        "lattice_vectors_selected": terms_selected,
        "full_lattice_determinant": fraction_string(full),
    }


class EvidenceCase:
    def __init__(self, identifier: str, group: str, details: dict | None = None):
        self.id = identifier
        self.group = group
        self.details = {"evidence_role": "supporting_only", **(details or {})}
        self.comparisons: list[dict[str, str]] = []

    def compare(self, left: int | Q, right: int | Q, label: str) -> None:
        self.comparisons.append({"left": fraction_string(left), "right": fraction_string(right),
                                 "label": label})

    def serialize(self, bindings: dict[str, list[str]]) -> dict:
        passed = bool(self.comparisons) and all(Q(c["left"]) == Q(c["right"])
                                               for c in self.comparisons)
        return {"id": self.id, "claims": bindings.get(self.group, []),
                "status": "pass" if passed else "fail", "details": self.details,
                "comparisons": self.comparisons}


def primary_case_id(kind: str, n: int, k: int, p: Q, seed: int) -> str:
    return f"identity-{kind}-n{n}-k{k}-p{parameter_tag(p)}-seed{seed}"


def primary_cases() -> list[EvidenceCase]:
    cases = []
    for kind in KINDS:
        for n in range(1, 4):
            for k in range(4):
                for parameter in parameter_values(kind):
                    for seed_index, seed in enumerate(SEEDS):
                        transformations = orbit(seed[:n])
                        case = EvidenceCase(primary_case_id(kind, n, k, parameter, seed_index),
                                            "width_zero" if k == 0 else kind, {
                            "type": kind, "n": n, "k": k,
                            "parameter_symbol": "tau" if kind in SQUARE_ROOT_KINDS else "t",
                            "parameter": fraction_string(parameter),
                            "seed": [fraction_string(z) for z in seed[:n]],
                            "source_anchor": SOURCE_ANCHORS[kind],
                            "transformation_count": len(transformations),
                        })
                        bounds = None
                        vectors = 0
                        for index, x in enumerate(transformations):
                            left = weyl_sum(kind, n, k, parameter, x)
                            row_value, explicit_value, diagnostic = affine_evaluations(
                                kind, n, k, parameter, x)
                            case.compare(left, row_value, f"orbit[{index}]: full Weyl vs row-sum determinant")
                            case.compare(left, explicit_value, f"orbit[{index}]: full Weyl vs explicit y lattice")
                            if kind == "Ct" and k:
                                case.compare(Q(diagnostic["full_lattice_determinant"]), Q(0),
                                             f"orbit[{index}]: last-column cancellation on full lattice")
                            bounds = diagnostic.get("row_bounds", [])
                            vectors += diagnostic.get("lattice_vectors_visited", 0)
                        case.details["row_bounds"] = bounds
                        case.details["lattice_vectors_visited_all_transforms"] = vectors
                        cases.append(case)
    return cases


def ct_zero_cases() -> list[EvidenceCase]:
    cases = []
    for n in range(1, 4):
        for k in range(1, 4):
            x = SEEDS[0][:n]
            coefficients = generating_coefficients(x)
            classical = determinant_leibniz([[extended(coefficients, n - i + j) -
                                             extended(coefficients, n + i + j)
                                             for j in range(1, k + 1)]
                                            for i in range(1, k + 1)])
            rows, lattice, _ = affine_evaluations("Ct", n, k, Q(0), x)
            case = EvidenceCase(f"boundary-Ct-t0-n{n}-k{k}", "Ct_zero", {
                "source_anchor": SOURCE_ANCHORS["Ct_zero"],
                "nonzero_shift": "j=k,y=1 has exponent k-k=0; it is retained before parity projection",
            })
            case.compare(rows, classical, "Ct t=0 parity determinant vs classical symplectic determinant")
            case.compare(lattice, classical, "Ct t=0 even lattice vs classical symplectic determinant")
            for i in range(1, k + 1):
                shifted = affine_weight("Ct", k, k, 1, Q(0)) * row_kernel(
                    "Ct", n, i, -k, coefficients)
                unshifted = row_kernel("Ct", n, i, k, coefficients)
                case.compare(shifted, -unshifted, f"last-column zero-exponent reflected term i={i}")
            cases.append(case)
    return cases


def expect_domain_error(function: Callable[[], Q]) -> tuple[int, str]:
    try:
        function()
    except DomainError as error:
        return 1, str(error)
    return 0, "displayed singular evaluation was accepted"


def domain_cases() -> list[EvidenceCase]:
    inputs = (
        ("zero-variable", "Bplus", 1, 1, Q(2, 3), (Q(0),)),
        ("coincident-variables", "C0", 2, 1, Q(2, 3), (Q(2), Q(2))),
        ("reciprocal-variables", "C0", 2, 1, Q(2, 3), (Q(2), Q(1, 2))),
        ("C-rho-one", "C0", 1, 1, Q(2, 3), (Q(1),)),
        ("C-rho-minus-one", "Ct", 1, 1, Q(2, 3), (Q(-1),)),
        ("B-rho-one", "B0", 1, 1, Q(2, 3), (Q(1),)),
        ("Weyl-normalization-zero", "Bplus", 2, 1, Q(-1), (Q(2), Q(3))),
        ("Ct-width0-normalization-zero", "Ct", 1, 0, Q(-1), (Q(2),)),
        ("Bt-width0-normalization-zero", "Bt", 1, 0, Q(-1), (Q(2),)),
        ("Bminus-width0-normalization-zero", "Bminus", 1, 0, Q(1), (Q(2),)),
    )
    cases = []
    for label, kind, n, k, parameter, x in inputs:
        rejected, reason = expect_domain_error(lambda: weyl_sum(kind, n, k, parameter, x))
        case = EvidenceCase(f"domain-{label}", "domain", {
            "type": kind, "n": n, "k": k, "parameter": fraction_string(parameter),
            "x": list(map(fraction_string, x)), "rejection_reason": reason,
            "meaning": "reject the displayed numerical rational expression; no claim about its cancelled extension",
        })
        case.compare(rejected, 1, "zero denominator causes explicit DomainError")
        if k == 0:
            # The normalized endpoint exists even when raw (2.1) cannot be substituted.
            endpoint, explicit_endpoint, _ = affine_evaluations(kind, n, 0, parameter, x)
            case.compare(endpoint, Q(1), "normalized empty endpoint after cancellation")
            case.compare(explicit_endpoint, Q(1), "empty vector convention")
        cases.append(case)
    return cases


def fault_case(identifier: str, correct: Q, mutant: Q, independent_reference: Q,
               mutation: str, *, detector_reference: Q | None = None,
               detector_path: str = "complete Weyl sum (2.1)") -> EvidenceCase:
    detector = independent_reference if detector_reference is None else detector_reference
    case = EvidenceCase(identifier, "faults", {
        "mutation": mutation, "correct": fraction_string(correct),
        "mutant": fraction_string(mutant), "difference": fraction_string(mutant - correct),
        "expected_counterexample": True, "independent_detector_path": detector_path,
        "independent_detector_value": fraction_string(detector),
    })
    case.compare(correct, independent_reference, "unmutated result agrees with independent path")
    case.compare(int(mutant != detector), 1,
                 "independent exact detector rejects deliberately wrong result")
    return case


def fault_cases() -> list[EvidenceCase]:
    cases = []
    for kind in ("Bplus", "Bt"):
        parameter, x = Q(2, 3), (Q(2),)
        correct, _, _ = affine_evaluations(kind, 1, 1, parameter, x)
        reference = weyl_sum(kind, 1, 1, parameter, x)
        cases.append(fault_case(f"mutation-missing-half-{kind}", correct, 2 * correct, reference,
                                "omit the external 1/2 at positive width"))
        endpoint = weyl_sum(kind, 1, 0, parameter, x)
        cases.append(fault_case(f"counterexample-width0-half-{kind}", Q(1), Q(1, 2), endpoint,
                                "apply the positive-width half-determinant display at width zero"))
    x, parameter = (Q(2),), Q(2, 3)
    correct, _, diagnostic = affine_evaluations("Ct", 1, 1, parameter, x)
    cases.append(fault_case("mutation-Ct-full-instead-even", correct,
                            Q(diagnostic["full_lattice_determinant"]),
                            weyl_sum("Ct", 1, 1, parameter, x),
                            "replace the even-sum sublattice by the full integer lattice"))
    for kind in ("BC", "Bminus"):
        x = (Q(2), Q(3))
        correct, _, _ = affine_evaluations(kind, 2, 1, parameter, x)
        cases.append(fault_case(f"mutation-tau-square-{kind}", correct,
                                weyl_sum(kind, 2, 1, parameter, x, pair_parameter=parameter),
                                weyl_sum(kind, 2, 1, parameter, x),
                                "use t=tau instead of t=tau^2 in the Weyl pair factors and V_n",
                                detector_reference=correct, detector_path="coefficient affine sum (1.4)/(1.8)"))
        cases.append(fault_case(f"mutation-tau-sign-{kind}", correct,
                                weyl_sum(kind, 2, 1, parameter, x, boundary_parameter=-parameter),
                                weyl_sum(kind, 2, 1, parameter, x),
                                "replace the boundary factor 1+tau*z by 1-tau*z",
                                detector_reference=correct, detector_path="coefficient affine sum (1.4)/(1.8)"))
    x, n, k = (Q(2), Q(3)), 2, 1
    coefficients = generating_coefficients(x)
    lo, hi = support_bounds("B0", n, k, 1)
    # The wrong second index is n+i+m, in place of n+i+m-1.
    wrong = sum((affine_weight("B0", k, 1, y, parameter) * (
        extended(coefficients, n - 1 + 1 - (2 * k + 1) * y) +
        extended(coefficients, n + 1 + 1 - (2 * k + 1) * y))
                 for y in range(lo, hi + 1)), Q(0))
    correct, _, _ = affine_evaluations("B0", n, k, parameter, x)
    cases.append(fault_case("mutation-kernel-index", correct, wrong,
                            weyl_sum("B0", n, k, parameter, x),
                            "raise the second h_i coefficient index by one"))
    x = (Q(2),)
    correct, _, _ = affine_evaluations("Ct", 1, 1, Q(0), x)
    coefficients = generating_coefficients(x)
    wrong = row_kernel("Ct", 1, 1, 1, coefficients) / 2
    cases.append(fault_case("mutation-Ct-t0-drop-zero-exponent-shift", correct, wrong,
                            weyl_sum("Ct", 1, 1, Q(0), x),
                            "drop every y!=0 before taking one half of the signed determinant at t=0"))
    return cases


def required_case_ids() -> list[str]:
    identifiers = [primary_case_id(kind, n, k, parameter, seed)
                   for kind in KINDS for n in range(1, 4) for k in range(4)
                   for parameter in parameter_values(kind) for seed in range(2)]
    identifiers += [f"boundary-Ct-t0-n{n}-k{k}" for n in range(1, 4) for k in range(1, 4)]
    identifiers += [case.id for case in domain_cases() + fault_cases()]
    return identifiers


def make_manifest() -> dict:
    return {
        "schema_version": 1,
        "evidence_role": "supporting_only",
        "independence_attestation": (
            "Implemented from authoritative.pdf/.txt and protocol.json only; experiments.py was inspected "
            "as an output-helper interface. No Lean implementation, specifications, reviews, README, "
            "canonical claims or previous experiment logs were read."),
        "inputs": input_hashes(),
        "runner": "scripts/fidelity/exact_experiments.py",
        "required_cases": required_case_ids(),
        "claim_bindings": {group: [] for group in SOURCE_ANCHORS},
        "claim_binding_source_anchors": SOURCE_ANCHORS,
        "coverage": {
            "types": list(KINDS), "ranks": [1, 2, 3], "widths": [0, 1, 2, 3],
            "ordinary_t": ["0", "1", "2/3", "-2/3"], "square_root_tau": ["0", "2/3", "-2/3"],
            "seeds": [[fraction_string(z) for z in seed] for seed in SEEDS],
            "variable_transformations": "truncate to rank; all n! permutations and all 2^n independent inversions",
            "explicit_lattice": "all widths 1..3; exact support-derived finite row ranges; Ct even lattice",
            "width_zero": "complete normalized Weyl sum versus normalized empty determinant; no Bplus/Bt half-factor",
        },
    }


def run_experiments(bindings: dict[str, list[str]] | None = None) -> dict:
    cases = primary_cases() + ct_zero_cases() + domain_cases() + fault_cases()
    entries = [case.serialize(bindings or {}) for case in cases]
    return {"schema_version": 1, "arithmetic": "exact", "cases": entries, "open_issues": []}


def save_json(path: Path, content: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(content, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="protocol exact-experiment JSON output")
    parser.add_argument("--write-manifest", action="store_true",
                        help="write the full required-case manifest with initially unbound claims")
    arguments = parser.parse_args()
    if arguments.write_manifest:
        save_json(ROOT / "fidelity/experiments.json", make_manifest())
    if arguments.output is None:
        if arguments.write_manifest:
            return 0
        parser.error("--output is required unless only --write-manifest is requested")
    manifest_path = ROOT / "fidelity/experiments.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8")) if manifest_path.exists() else make_manifest()
    report = run_experiments(manifest.get("claim_bindings", {}))
    observed_ids = [case["id"] for case in report["cases"]]
    if set(observed_ids) != set(manifest["required_cases"]) or len(observed_ids) != len(set(observed_ids)):
        report["open_issues"].append("Manifest and runner case inventories differ or contain duplicates")
    if manifest.get("inputs") != input_hashes():
        report["open_issues"].append("Authoritative inputs differ from the recorded manifest hashes")
    save_json(arguments.output, report)
    passed = sum(case["status"] == "pass" for case in report["cases"])
    comparisons = sum(len(case["comparisons"]) for case in report["cases"])
    print(json.dumps({"cases": len(report["cases"]), "passed": passed,
                      "comparisons": comparisons, "open_issues": report["open_issues"],
                      "evidence_role": "supporting_only", "output": str(arguments.output)}, ensure_ascii=False))
    return 0 if report["cases"] and passed == len(report["cases"]) and not report["open_issues"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
