"""Self-tests for the independently implemented supporting experiments."""
import importlib.util
from fractions import Fraction as Q
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "independent_exact_experiments", ROOT / "scripts/fidelity/exact_experiments.py")
E = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(E)


class ExactExperimentsTest(unittest.TestCase):
    def test_determinants_use_independent_algorithms(self):
        matrices = ([], [[Q(7)]], [[Q(0), Q(2)], [Q(3), Q(4)]],
                    [[Q(1), Q(2), Q(3)], [Q(2), Q(4), Q(6)], [Q(7), Q(8), Q(10)]],
                    [[Q(1, 2), Q(2), Q(-3)], [Q(2), Q(1, 3), Q(4)],
                     [Q(0), Q(5), Q(7, 3)]])
        for matrix in matrices:
            self.assertEqual(E.determinant_elimination(matrix), E.determinant_leibniz(matrix))
        self.assertEqual(E.determinant_elimination([]), 1)
        self.assertEqual(E.determinant_leibniz([]), 1)
        self.assertEqual(E.determinant_elimination(matrices[2]), -6)
        self.assertEqual(E.determinant_elimination(matrices[3]), 0)

    def test_coefficients_and_zero_extension(self):
        dot = E.generating_coefficients((Q(2),))
        self.assertEqual(dot, (Q(1), Q(5, 2), Q(1)))
        self.assertEqual(E.generating_coefficients((Q(2),), True),
                         (Q(1), Q(7, 2), Q(7, 2), Q(1)))
        self.assertEqual(E.extended(dot, -1), 0)
        self.assertEqual(E.extended(dot, 3), 0)
        for n in range(1, 4):
            coefficients = E.generating_coefficients(E.SEEDS[0][:n])
            self.assertEqual(coefficients, tuple(reversed(coefficients)))

    def test_support_derived_bounds_exclude_only_zero_rows(self):
        for kind in E.KINDS:
            for n in range(1, 4):
                for k in range(1, 4):
                    coefficients = E.generating_coefficients(E.SEEDS[0][:n], kind == "Bt")
                    period = E.affine_period(kind, k)
                    degree = len(coefficients) - 1
                    delta = E.kernel_delta(kind)
                    for i in range(1, k + 1):
                        lower, upper = E.support_bounds(kind, n, k, i)
                        for y in (lower - 1, upper + 1):
                            for j in range(1, k + 1):
                                indices = (n - i + j - period * y,
                                           n + i + j - period * y - delta)
                                self.assertTrue(all(r > degree for r in indices) or
                                                all(r < 0 for r in indices))
                                self.assertEqual(E.row_kernel(kind, n, i, j - period * y,
                                                              coefficients), 0)

    def test_width_zero_never_evaluates_entries_or_half_factor(self):
        with patch.object(E, "row_kernel", side_effect=AssertionError("kernel evaluated")), \
             patch.object(E, "affine_weight", side_effect=AssertionError("weight evaluated")), \
             patch.object(E, "support_bounds", side_effect=AssertionError("bound evaluated")):
            for kind in E.KINDS:
                self.assertEqual(E.affine_evaluations(kind, 1, 0, Q(0), (Q(2),))[:2], (Q(1), Q(1)))
        for kind in E.KINDS:
            self.assertEqual(E.weyl_sum(kind, 2, 0, Q(2, 3), (Q(2), Q(3))), 1)

    def test_Ct_zero_parameter_retains_nonzero_shift(self):
        coefficients = E.generating_coefficients((Q(2),))
        shifted = E.affine_weight("Ct", 1, 1, 1, Q(0)) * E.row_kernel("Ct", 1, 1, -1, coefficients)
        self.assertEqual(shifted, Q(-5, 2))
        rows, grid, diagnostic = E.affine_evaluations("Ct", 1, 1, Q(0), (Q(2),))
        self.assertEqual(rows, Q(5, 2))
        self.assertEqual(grid, Q(5, 2))
        self.assertEqual(Q(diagnostic["full_lattice_determinant"]), 0)

    def test_raw_domain_rejections_and_normalized_endpoints(self):
        cases = E.domain_cases()
        self.assertEqual(len(cases), 10)
        self.assertTrue(all(case.serialize({})["status"] == "pass" for case in cases))

    def test_every_deliberate_fault_is_detected(self):
        cases = E.fault_cases()
        self.assertEqual(len(cases), 11)
        for case in cases:
            self.assertEqual(case.serialize({})["status"], "pass", case.id)
            self.assertNotEqual(Q(case.details["mutant"]), Q(case.details["correct"]), case.id)

    def test_seven_types_nontrivial_rank_three(self):
        for kind in E.KINDS:
            parameter = Q(-2, 3)
            x = (Q(-2), Q(3), Q(-5))
            weyl = E.weyl_sum(kind, 3, 3, parameter, x)
            row_value, lattice, _ = E.affine_evaluations(kind, 3, 3, parameter, x)
            self.assertEqual(weyl, row_value, kind)
            self.assertEqual(weyl, lattice, kind)

    def test_manifest_cases_are_unique_and_bindings_initially_explicit(self):
        manifest = E.make_manifest()
        identifiers = manifest["required_cases"]
        self.assertEqual(len(identifiers), len(set(identifiers)))
        self.assertEqual(len(identifiers), 654)
        self.assertTrue(all(value == [] for value in manifest["claim_bindings"].values()))


if __name__ == "__main__":
    unittest.main()
