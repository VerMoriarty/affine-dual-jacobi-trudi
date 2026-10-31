import AffineDualJT.PaperAlternantDivisibility
import Mathlib.LinearAlgebra.Vandermonde

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-!
# Lowest-degree normalization for Lemma 2.1

The original proof fixes the scalar left over from factor divisibility by
comparing lowest homogeneous parts.  We encode homogeneous degree by scaling
every variable by one auxiliary polynomial variable.  This module develops
the column factorization needed to extract that lowest-degree coefficient.
-/

namespace AffineDualJT
open scoped BigOperators
open Polynomial
noncomputable section
variable {F : Type*} [Field F]

abbrev PaperScaledPoly (n : ℕ) := Polynomial (MvPolynomial (Fin n) F)

/-- Simultaneous scaling `X_a ↦ y X_a`; the coefficient ring is embedded
unchanged into the auxiliary polynomial ring. -/
def paperScaleHom {n : ℕ} : MvPolynomial (Fin n) F →+* PaperScaledPoly (F := F) n :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.C : F →+* MvPolynomial (Fin n) F))
    (fun a => Polynomial.X * Polynomial.C (MvPolynomial.X a : MvPolynomial (Fin n) F))

def paperBasicScaledReduced {n : ℕ} (t : F) (a r : Fin n) : PaperScaledPoly (F := F) n :=
  if r.val = 0 then Polynomial.C (MvPolynomial.X a ^ (n - 1)) else
    Polynomial.C (MvPolynomial.X a ^ (n - (r.val + 1))) +
      Polynomial.X ^ (2 * r.val) *
        Polynomial.C ((MvPolynomial.C t) ^ r.val * MvPolynomial.X a ^ (n + r.val - 1))

def paperCtScaledReduced {n : ℕ} (t : F) (a r : Fin n) : PaperScaledPoly (F := F) n :=
  Polynomial.C (MvPolynomial.X a ^ (n - (r.val + 1))) -
    Polynomial.X ^ (2 * (r.val + 1)) *
      Polynomial.C ((MvPolynomial.C t) ^ (r.val + 1) *
        MvPolynomial.X a ^ (n + r.val + 1))

def paperBminusScaledReduced {n : ℕ} (τ : F) (a r : Fin n) : PaperScaledPoly (F := F) n :=
  Polynomial.C (MvPolynomial.X a ^ (n - (r.val + 1))) +
    Polynomial.X ^ (2 * r.val + 1) *
      Polynomial.C ((MvPolynomial.C τ) ^ (2 * r.val + 1) *
        MvPolynomial.X a ^ (n + r.val))

theorem paper_scale_fColumn {n : ℕ} (t : F) (a r : Fin n) :
    paperScaleHom (fColumn (MvPolynomial.C t) r
      (MvPolynomial.X a : MvPolynomial (Fin n) F)) =
      Polynomial.X ^ (n - (r.val + 1)) * paperBasicScaledReduced t a r := by
  classical
  by_cases hz : r.val = 0
  · simp [paperScaleHom, fColumn, paperBasicScaledReduced, hz, map_pow, mul_pow]
    ring
  · simp [paperScaleHom, fColumn, paperBasicScaledReduced, hz, map_pow, map_mul, map_add,
      mul_pow]
    have he : n + r.val - 1 = (n - (r.val + 1)) + 2 * r.val := by omega
    rw [he, pow_add]
    ring

theorem paper_scale_ctColumn {n : ℕ} (t : F) (a r : Fin n) :
    paperScaleHom (ctAlternantColumn (MvPolynomial.C t) r
      (MvPolynomial.X a : MvPolynomial (Fin n) F)) =
      Polynomial.X ^ (n - (r.val + 1)) * paperCtScaledReduced t a r := by
  classical
  simp [paperScaleHom, ctAlternantColumn, paperCtScaledReduced, map_pow, map_mul,
    map_sub, mul_pow]
  have he : n + r.val + 1 = n - (r.val + 1) + 2 * (r.val + 1) := by omega
  rw [he, pow_add]
  ring

theorem paper_scale_bminusColumn {n : ℕ} (τ : F) (a r : Fin n) :
    paperScaleHom (bminusAlternantColumn (MvPolynomial.C τ) r
      (MvPolynomial.X a : MvPolynomial (Fin n) F)) =
      Polynomial.X ^ (n - (r.val + 1)) * paperBminusScaledReduced τ a r := by
  classical
  simp [paperScaleHom, bminusAlternantColumn, paperBminusScaledReduced, map_pow,
    map_mul, map_add, mul_pow]
  have he : n + r.val = n - (r.val + 1) + (2 * r.val + 1) := by omega
  rw [he, pow_add]
  ring

def paperBasicScaledMatrix {n : ℕ} (t : F) :
    Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n) :=
  Matrix.of fun a r => paperBasicScaledReduced t a r

def paperCtScaledMatrix {n : ℕ} (t : F) :
    Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n) :=
  Matrix.of fun a r => paperCtScaledReduced t a r

def paperBminusScaledMatrix {n : ℕ} (τ : F) :
    Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n) :=
  Matrix.of fun a r => paperBminusScaledReduced τ a r

def paperBasicScaledNtRest {n : ℕ} (t : F) (p : paperAlternantPairIndex n) :
    PaperScaledPoly (F := F) n :=
  Polynomial.C (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) *
    (1 - Polynomial.C (MvPolynomial.C t) * Polynomial.X ^ 2 *
      Polynomial.C (MvPolynomial.X p.1) * Polynomial.C (MvPolynomial.X p.2.1))

theorem paper_basic_lower_exponent_sum (n : ℕ) :
    (∑ r : Fin n, (n - (r.val + 1))) = n * (n - 1) / 2 := by
  have hsum : (∑ r : Fin n, (n - (r.val + 1))) =
      ∑ i ∈ Finset.range n, (n - (i + 1)) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => n - (i + 1)) n)
  rw [hsum]
  calc
    (∑ i ∈ Finset.range n, (n - (i + 1))) =
        ∑ i ∈ Finset.range n, (n - 1 - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          omega
    _ = ∑ i ∈ Finset.range n, i :=
          Finset.sum_range_reflect (fun i : ℕ => i) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

theorem paper_scale_Nt {n : ℕ} (t : F) :
    paperScaleHom (Nt (R := MvPolynomial (Fin n) F) (n := n) (MvPolynomial.C t)
      (MvPolynomial.X (R := F))) =
      Polynomial.X ^ (Fintype.card (paperAlternantPairIndex n)) *
        (∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest t p) := by
  classical
  have hterms : paperScaleHom (Nt (R := MvPolynomial (Fin n) F) (n := n)
      (MvPolynomial.C t) (MvPolynomial.X (R := F))) =
      ∏ p : paperAlternantPairIndex n, Polynomial.X * paperBasicScaledNtRest t p := by
    simp [Nt, paperScaleHom, paperBasicScaledNtRest, paperAlternantPairIndex,
      Fintype.prod_sigma, map_prod, map_mul, map_sub, map_one]
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    ring
  rw [hterms, Finset.prod_mul_distrib]
  simp [Finset.prod_const]

theorem paper_Nt_scale_lowest_coeff {n : ℕ} (t : F) :
    Polynomial.coeff (paperScaleHom (Nt (R := MvPolynomial (Fin n) F) (n := n)
      (MvPolynomial.C t) (MvPolynomial.X (R := F)))) (n * (n - 1) / 2) =
      ∏ p : paperAlternantPairIndex n,
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
  rw [paper_scale_Nt, paper_alternant_pairIndex_card_eq_triangular]
  calc
    _ = (∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest t p).coeff 0 := by
      simpa only [zero_add] using
        (Polynomial.coeff_X_pow_mul
          (∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest t p)
          (n * (n - 1) / 2) 0)
    _ = Polynomial.eval 0 (∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest t p) :=
      Polynomial.coeff_zero_eq_eval_zero _
    _ = _ := by simp [paperBasicScaledNtRest, Polynomial.eval_prod]

theorem paper_coeff_row_mul_X_pow {R : Type*} [CommSemiring R]
    (f g : Polynomial R) (d : ℕ) :
    Polynomial.coeff (f * (Polynomial.X ^ d * g)) d = Polynomial.coeff (f * g) 0 := by
  rw [show f * (Polynomial.X ^ d * g) = Polynomial.X ^ d * (f * g) by ring]
  simpa only [zero_add] using Polynomial.coeff_X_pow_mul (f * g) d 0

theorem paper_ct_factor_scale_lowest_coeff {n : ℕ} (t : F) :
    Polynomial.coeff (paperScaleHom (paperCtFactorProduct (n := n) t))
      (n * (n - 1) / 2) =
      ∏ p : paperAlternantPairIndex n,
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
  rw [paper_ct_factor_product_eq]
  simp only [map_mul, map_prod]
  rw [paper_scale_Nt, paper_alternant_pairIndex_card_eq_triangular]
  let R : PaperScaledPoly (F := F) n :=
    ∏ a : Fin n, paperScaleHom
      (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2)
  let G : PaperScaledPoly (F := F) n :=
    ∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest t p
  change Polynomial.coeff (R * (Polynomial.X ^ (n * (n - 1) / 2) * G))
    (n * (n - 1) / 2) = _
  rw [paper_coeff_row_mul_X_pow, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul]
  have hR : Polynomial.eval 0 R = 1 := by
    simp [R, paperScaleHom, Polynomial.eval_prod]
  have hG : Polynomial.eval 0 G =
      ∏ p : paperAlternantPairIndex n, (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
    simp [G, paperBasicScaledNtRest, Polynomial.eval_prod]
  rw [hR, hG]
  simp

theorem paper_bminus_factor_scale_lowest_coeff {n : ℕ} (τ : F) :
    Polynomial.coeff (paperScaleHom (paperBminusFactorProduct (n := n) τ))
      (n * (n - 1) / 2) =
      ∏ p : paperAlternantPairIndex n,
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
  rw [paper_bminus_factor_product_eq]
  simp only [map_mul, map_prod]
  rw [paper_scale_Nt, paper_alternant_pairIndex_card_eq_triangular]
  let R : PaperScaledPoly (F := F) n :=
    ∏ a : Fin n, paperScaleHom
      (1 + MvPolynomial.C τ * MvPolynomial.X a)
  let G : PaperScaledPoly (F := F) n :=
    ∏ p : paperAlternantPairIndex n, paperBasicScaledNtRest (τ ^ 2) p
  change Polynomial.coeff (R * (Polynomial.X ^ (n * (n - 1) / 2) * G))
    (n * (n - 1) / 2) = _
  rw [paper_coeff_row_mul_X_pow, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul]
  have hR : Polynomial.eval 0 R = 1 := by
    simp [R, paperScaleHom, Polynomial.eval_prod]
  have hG : Polynomial.eval 0 G =
      ∏ p : paperAlternantPairIndex n, (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
    simp [G, paperBasicScaledNtRest, Polynomial.eval_prod]
  rw [hR, hG]
  simp

theorem paper_scale_basic_alternant {n : ℕ} (t : F) :
    paperScaleHom (paperBasicAlternantPolynomial (n := n) t) =
      Polynomial.X ^ (n * (n - 1) / 2) * (paperBasicScaledMatrix t).det := by
  classical
  have hmat : (Matrix.of fun a r => paperScaleHom
      (fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
        Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) =
      (Matrix.of fun a r => Polynomial.X ^ (n - (r.val + 1)) *
        paperBasicScaledReduced t a r :
          Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) := by
    apply Matrix.ext
    intro a r
    exact paper_scale_fColumn t a r
  calc
    paperScaleHom (paperBasicAlternantPolynomial (n := n) t) =
        (Matrix.of fun a r => paperScaleHom
          (fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
            Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)).det := by
            change paperScaleHom (Matrix.det (Matrix.of fun a r =>
              fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F))) = _
            rw [RingHom.map_det]
            rfl
    _ = (∏ r : Fin n, Polynomial.X ^ (n - (r.val + 1))) *
        (paperBasicScaledMatrix t).det := by
          rw [hmat]
          simpa [paperBasicScaledMatrix] using
            (Matrix.det_mul_row (fun r : Fin n => Polynomial.X ^ (n - (r.val + 1)))
              (paperBasicScaledMatrix t))
    _ = _ := by
          rw [Finset.prod_pow_eq_pow_sum, paper_basic_lower_exponent_sum]

theorem paper_scale_ct_alternant {n : ℕ} (t : F) :
    paperScaleHom (paperCtAlternantPolynomial (n := n) t) =
      Polynomial.X ^ (n * (n - 1) / 2) * (paperCtScaledMatrix t).det := by
  classical
  have hmat : (Matrix.of fun a r => paperScaleHom
      (ctAlternantColumn (MvPolynomial.C t) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
        Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) =
      (Matrix.of fun a r => Polynomial.X ^ (n - (r.val + 1)) *
        paperCtScaledReduced t a r :
          Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) := by
    apply Matrix.ext
    intro a r
    exact paper_scale_ctColumn t a r
  calc
    paperScaleHom (paperCtAlternantPolynomial (n := n) t) =
        (Matrix.of fun a r => paperScaleHom
          (ctAlternantColumn (MvPolynomial.C t) r
            (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
            Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)).det := by
            change paperScaleHom (Matrix.det (Matrix.of fun a r =>
              ctAlternantColumn (MvPolynomial.C t) r
                (MvPolynomial.X a : MvPolynomial (Fin n) F))) = _
            rw [RingHom.map_det]
            rfl
    _ = (∏ r : Fin n, Polynomial.X ^ (n - (r.val + 1))) *
        (paperCtScaledMatrix t).det := by
          rw [hmat]
          simpa [paperCtScaledMatrix] using
            (Matrix.det_mul_row (fun r : Fin n => Polynomial.X ^ (n - (r.val + 1)))
              (paperCtScaledMatrix t))
    _ = _ := by
          rw [Finset.prod_pow_eq_pow_sum, paper_basic_lower_exponent_sum]

theorem paper_scale_bminus_alternant {n : ℕ} (τ : F) :
    paperScaleHom (paperBminusAlternantPolynomial (n := n) τ) =
      Polynomial.X ^ (n * (n - 1) / 2) * (paperBminusScaledMatrix τ).det := by
  classical
  have hmat : (Matrix.of fun a r => paperScaleHom
      (bminusAlternantColumn (MvPolynomial.C τ) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
        Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) =
      (Matrix.of fun a r => Polynomial.X ^ (n - (r.val + 1)) *
        paperBminusScaledReduced τ a r :
          Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)) := by
    apply Matrix.ext
    intro a r
    exact paper_scale_bminusColumn τ a r
  calc
    paperScaleHom (paperBminusAlternantPolynomial (n := n) τ) =
        (Matrix.of fun a r => paperScaleHom
          (bminusAlternantColumn (MvPolynomial.C τ) r
            (MvPolynomial.X a : MvPolynomial (Fin n) F)) :
            Matrix (Fin n) (Fin n) (PaperScaledPoly (F := F) n)).det := by
            change paperScaleHom (Matrix.det (Matrix.of fun a r =>
              bminusAlternantColumn (MvPolynomial.C τ) r
                (MvPolynomial.X a : MvPolynomial (Fin n) F))) = _
            rw [RingHom.map_det]
            rfl
    _ = (∏ r : Fin n, Polynomial.X ^ (n - (r.val + 1))) *
        (paperBminusScaledMatrix τ).det := by
          rw [hmat]
          simpa [paperBminusScaledMatrix] using
            (Matrix.det_mul_row (fun r : Fin n => Polynomial.X ^ (n - (r.val + 1)))
              (paperBminusScaledMatrix τ))
    _ = _ := by
          rw [Finset.prod_pow_eq_pow_sum, paper_basic_lower_exponent_sum]

theorem paper_basic_scaled_reduced_eval_zero {n : ℕ} (t : F) (a r : Fin n) :
    Polynomial.eval 0 (paperBasicScaledReduced t a r) =
      MvPolynomial.X a ^ (n - (r.val + 1)) := by
  by_cases hr : r.val = 0
  · have he : n - 1 = n - (r.val + 1) := by omega
    simp [paperBasicScaledReduced, hr, he]
  · simp [paperBasicScaledReduced, hr]

theorem paper_ct_scaled_reduced_eval_zero {n : ℕ} (t : F) (a r : Fin n) :
    Polynomial.eval 0 (paperCtScaledReduced t a r) =
      MvPolynomial.X a ^ (n - (r.val + 1)) := by
  simp [paperCtScaledReduced]

theorem paper_bminus_scaled_reduced_eval_zero {n : ℕ} (τ : F) (a r : Fin n) :
    Polynomial.eval 0 (paperBminusScaledReduced τ a r) =
      MvPolynomial.X a ^ (n - (r.val + 1)) := by
  simp [paperBminusScaledReduced]

theorem paper_basic_scaled_det_eval_zero {n : ℕ} (t : F) :
    Polynomial.eval 0 (paperBasicScaledMatrix t).det =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  change (Polynomial.evalRingHom (0 : MvPolynomial (Fin n) F))
    (paperBasicScaledMatrix t).det = _
  rw [RingHom.map_det]
  change (Matrix.of fun a r => Polynomial.eval 0 (paperBasicScaledReduced t a r)).det = _
  simp [paper_basic_scaled_reduced_eval_zero]

theorem paper_ct_scaled_det_eval_zero {n : ℕ} (t : F) :
    Polynomial.eval 0 (paperCtScaledMatrix t).det =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  change (Polynomial.evalRingHom (0 : MvPolynomial (Fin n) F))
    (paperCtScaledMatrix t).det = _
  rw [RingHom.map_det]
  change (Matrix.of fun a r => Polynomial.eval 0 (paperCtScaledReduced t a r)).det = _
  simp [paper_ct_scaled_reduced_eval_zero]

theorem paper_bminus_scaled_det_eval_zero {n : ℕ} (τ : F) :
    Polynomial.eval 0 (paperBminusScaledMatrix τ).det =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  change (Polynomial.evalRingHom (0 : MvPolynomial (Fin n) F))
    (paperBminusScaledMatrix τ).det = _
  rw [RingHom.map_det]
  change (Matrix.of fun a r => Polynomial.eval 0 (paperBminusScaledReduced τ a r)).det = _
  simp [paper_bminus_scaled_reduced_eval_zero]

theorem paper_basic_scale_lowest_coeff {n : ℕ} (t : F) :
    (paperScaleHom (paperBasicAlternantPolynomial (n := n) t)).coeff
        (n * (n - 1) / 2) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  rw [paper_scale_basic_alternant]
  calc
    _ = (paperBasicScaledMatrix t).det.coeff 0 := by
      simpa only [zero_add] using
        (Polynomial.coeff_X_pow_mul (paperBasicScaledMatrix t).det
          (n * (n - 1) / 2) 0)
    _ = Polynomial.eval 0 (paperBasicScaledMatrix t).det :=
      Polynomial.coeff_zero_eq_eval_zero _
    _ = _ := paper_basic_scaled_det_eval_zero t

theorem paper_ct_scale_lowest_coeff {n : ℕ} (t : F) :
    (paperScaleHom (paperCtAlternantPolynomial (n := n) t)).coeff
        (n * (n - 1) / 2) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  rw [paper_scale_ct_alternant]
  calc
    _ = (paperCtScaledMatrix t).det.coeff 0 := by
      simpa only [zero_add] using
        (Polynomial.coeff_X_pow_mul (paperCtScaledMatrix t).det
          (n * (n - 1) / 2) 0)
    _ = Polynomial.eval 0 (paperCtScaledMatrix t).det :=
      Polynomial.coeff_zero_eq_eval_zero _
    _ = _ := paper_ct_scaled_det_eval_zero t

theorem paper_bminus_scale_lowest_coeff {n : ℕ} (τ : F) :
    (paperScaleHom (paperBminusAlternantPolynomial (n := n) τ)).coeff
        (n * (n - 1) / 2) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det := by
  rw [paper_scale_bminus_alternant]
  calc
    _ = (paperBminusScaledMatrix τ).det.coeff 0 := by
      simpa only [zero_add] using
        (Polynomial.coeff_X_pow_mul (paperBminusScaledMatrix τ).det
          (n * (n - 1) / 2) 0)
    _ = Polynomial.eval 0 (paperBminusScaledMatrix τ).det :=
      Polynomial.coeff_zero_eq_eval_zero _
    _ = _ := paper_bminus_scaled_det_eval_zero τ

/-- Reversing the columns of the usual Vandermonde matrix gives the
descending-power determinant that occurs as the lowest homogeneous part in
the paper's normalization argument. -/
theorem paper_descending_vandermonde_eq_pair_product {n : ℕ} :
    (Matrix.of fun a r : Fin n =>
      (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))).det =
      ∏ p : paperAlternantPairIndex n,
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
  classical
  let v : Fin n → MvPolynomial (Fin n) F := fun a => MvPolynomial.X a
  let V : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) F) := Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) F) := Matrix.of fun a r =>
    (MvPolynomial.X a : MvPolynomial (Fin n) F) ^ (n - (r.val + 1))
  have hD : D = V.submatrix id Fin.revPerm := by
    ext a r
    simp [D, V, Matrix.vandermonde, v, Fin.revPerm_apply]
  have hdet : D.det = (Fin.revPerm : Equiv.Perm (Fin n)).sign *
      ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
        (MvPolynomial.X b - MvPolynomial.X a) := by
    rw [hD, Matrix.det_permute', Matrix.det_vandermonde]
  have hsign : (Fin.revPerm : Equiv.Perm (Fin n)).sign =
      (-1 : ℤˣ) ^ Fintype.card (paperAlternantPairIndex n) := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi, paper_alternant_pairIndex_card]
    have hterms : ∀ a : Fin n, ∀ b ∈ Finset.Ioi a,
        (if Fin.revPerm a < Fin.revPerm b then 1 else -1 : ℤˣ) = -1 := by
      intro a b hb
      have hab : a < b := Finset.mem_Ioi.mp hb
      have hnot : ¬ Fin.revPerm a < Fin.revPerm b := by
        rw [Fin.revPerm_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
        exact not_lt_of_ge hab.le
      exact ite_eq_right hnot
    calc
      (∏ x : Fin n, ∏ x_1 ∈ Finset.Ioi x,
          (if Fin.revPerm x < Fin.revPerm x_1 then 1 else -1 : ℤˣ)) =
          ∏ x : Fin n, ∏ x_1 ∈ Finset.Ioi x, (-1 : ℤˣ) := by
            apply Finset.prod_congr rfl
            intro a ha
            apply Finset.prod_congr rfl
            intro b hb
            exact hterms a b hb
      _ = _ := by
        have hinner (a : Fin n) :
            (∏ b ∈ Finset.Ioi a, (-1 : ℤˣ)) =
              (-1 : ℤˣ) ^ (Finset.Ioi a).card := by simp
        simp_rw [hinner]
        change (∏ a ∈ (Finset.univ : Finset (Fin n)),
          (-1 : ℤˣ) ^ (Finset.Ioi a).card) = _
        rw [Finset.prod_pow_eq_pow_sum]
        have hsum : (∑ a : Fin n, (Finset.Ioi a).card) =
            ∑ a : Fin n, Fintype.card {b : Fin n // a < b} := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Fin.card_Ioi, paper_fin_upper_card]
          simp [Nat.sub_sub, Nat.add_comm]
        rw [hsum]
  rw [hdet, hsign]
  have hneg : ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
      (MvPolynomial.X b - MvPolynomial.X a) =
      (-1 : MvPolynomial (Fin n) F) ^ Fintype.card (paperAlternantPairIndex n) *
        ∏ p : paperAlternantPairIndex n,
          (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
    have hprod :
        (∏ p : paperAlternantPairIndex n,
          (MvPolynomial.X (R := F) p.2.1 - MvPolynomial.X p.1)) =
        ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
          (MvPolynomial.X (R := F) b - MvPolynomial.X a) := by
      simp only [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro a ha
      let e : {b : Fin n // a < b} ≃ {b : Fin n // b ∈ Finset.Ioi a} := {
        toFun := fun b => ⟨b.1, Finset.mem_Ioi.mpr b.2⟩
        invFun := fun b => ⟨b.1, Finset.mem_Ioi.mp b.2⟩
        left_inv := by intro b; cases b; rfl
        right_inv := by intro b; cases b; rfl }
      calc
        (∏ b : {b : Fin n // a < b},
            (MvPolynomial.X (R := F) b.1 - MvPolynomial.X a)) =
            ∏ b : {b : Fin n // b ∈ Finset.Ioi a},
              (MvPolynomial.X (R := F) b.1 - MvPolynomial.X a) :=
                Fintype.prod_equiv e _ _ (by intro b; rfl)
        _ = ∏ b ∈ Finset.Ioi a,
              (MvPolynomial.X (R := F) b - MvPolynomial.X a) := by
                simpa only [Finset.mem_Ioi] using
                  (Finset.prod_coe_sort (Finset.Ioi a)
                    (fun b : Fin n => MvPolynomial.X (R := F) b - MvPolynomial.X a))
    calc
      (∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
          (MvPolynomial.X b - MvPolynomial.X a)) =
          ∏ p : paperAlternantPairIndex n,
            (MvPolynomial.X p.2.1 - MvPolynomial.X p.1) := hprod.symm
      _ = ∏ p : paperAlternantPairIndex n,
            (-(MvPolynomial.X p.1 - MvPolynomial.X p.2.1)) := by
              apply Finset.prod_congr rfl
              intro p hp
              ring
      _ = (∏ p : paperAlternantPairIndex n, (-1 : MvPolynomial (Fin n) F)) *
            ∏ p : paperAlternantPairIndex n,
              (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
              rw [← Finset.prod_mul_distrib]
              apply Finset.prod_congr rfl
              intro p hp
              ring
      _ = _ := by simp [Finset.prod_const]
  rw [hneg]
  norm_num
  rw [← mul_assoc, ← pow_add]
  have hdouble : (∑ i : Fin n, Fintype.card {b : Fin n // i < b}) +
      (∑ i : Fin n, Fintype.card {b : Fin n // i < b}) =
      2 * (∑ i : Fin n, Fintype.card {b : Fin n // i < b}) := by omega
  rw [hdouble, pow_mul]
  simp

theorem paper_basic_factor_scale_lowest_coeff {n : ℕ} (t : F) :
    Polynomial.coeff (paperScaleHom (paperBasicFactorProduct (n := n) t))
      (n * (n - 1) / 2) =
      ∏ p : paperAlternantPairIndex n,
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1) := by
  rw [paper_basic_factor_product_eq_Nt]
  exact paper_Nt_scale_lowest_coeff t

private theorem paper_pair_product_ne_zero {n : ℕ} :
    (∏ p : paperAlternantPairIndex n,
      (MvPolynomial.X p.1 - MvPolynomial.X p.2.1 : MvPolynomial (Fin n) F)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp hz
  have hdeg := paper_difference_factor_totalDegree (F := F) p.1 p.2.1
    (ne_of_lt p.2.2)
  rw [hz] at hdeg
  simp at hdeg

private theorem paper_normalize_scalar_from_lowest_coeff {n d : ℕ}
    (p q : MvPolynomial (Fin n) F) (hdiv : p ∣ q) (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : q.totalDegree ≤ p.totalDegree)
    (hDne : (∏ j : paperAlternantPairIndex n,
      ((MvPolynomial.X (R := F) j.1 : MvPolynomial (Fin n) F) -
        MvPolynomial.X j.2.1)) ≠ 0)
    (hpc : (paperScaleHom p).coeff d =
      ∏ j : paperAlternantPairIndex n,
        (MvPolynomial.X (R := F) j.1 - MvPolynomial.X j.2.1))
    (hqc : (paperScaleHom q).coeff d =
      ∏ j : paperAlternantPairIndex n,
        (MvPolynomial.X (R := F) j.1 - MvPolynomial.X j.2.1)) :
    q = p := by
  obtain ⟨c, hqpc⟩ := paper_scalar_quotient_of_dvd_of_totalDegree_le
    p q hdiv hp hq hdeg
  have hscale := congrArg paperScaleHom hqpc
  rw [map_mul] at hscale
  have hCmap : paperScaleHom (MvPolynomial.C (R := F) c : MvPolynomial (Fin n) F) =
      (Polynomial.C (MvPolynomial.C c) : Polynomial (MvPolynomial (Fin n) F)) := by
    simp [paperScaleHom]
  rw [hCmap] at hscale
  have hcoeff := congrArg (fun g : Polynomial (MvPolynomial (Fin n) F) => g.coeff d) hscale
  rw [Polynomial.coeff_mul_C] at hcoeff
  rw [hpc, hqc] at hcoeff
  have hC : (MvPolynomial.C c : MvPolynomial (Fin n) F) =
      (1 : MvPolynomial (Fin n) F) := by
    apply (mul_left_cancel₀ hDne)
    simpa using hcoeff.symm
  have hc : c = 1 := by
    exact (MvPolynomial.C_inj F c 1).mp hC
  rw [hqpc, hc]
  simp

theorem paper_basic_factorization_by_lowest_part {n : ℕ} (t : F) (ht : t ≠ 0) :
    paperBasicAlternantPolynomial (n := n) t = paperBasicFactorProduct t := by
  apply paper_normalize_scalar_from_lowest_coeff (n := n) (d := n * (n - 1) / 2)
    (paperBasicFactorProduct (n := n) t) (paperBasicAlternantPolynomial t)
    (paper_basic_full_factor_product_dvd t ht)
  · intro hz
    have hcoeff := paper_basic_factor_scale_lowest_coeff (n := n) t
    rw [hz] at hcoeff
    simp at hcoeff
    exact paper_pair_product_ne_zero (F := F) (n := n) hcoeff.symm
  · intro hz
    have hcoeff := paper_basic_scale_lowest_coeff (n := n) t
    rw [hz] at hcoeff
    simp at hcoeff
    have hD := paper_descending_vandermonde_eq_pair_product (F := F) (n := n)
    exact paper_pair_product_ne_zero (F := F) (n := n) (hD.symm ▸ hcoeff.symm)
  · rw [paper_basic_factor_product_totalDegree_eq t ht]
    exact paper_basic_alternant_totalDegree_le t
  · exact paper_pair_product_ne_zero (F := F) (n := n)
  · exact paper_basic_factor_scale_lowest_coeff (n := n) t
  · simpa only [paper_descending_vandermonde_eq_pair_product] using
      paper_basic_scale_lowest_coeff (n := n) t

theorem paper_ct_factorization_by_lowest_part {n : ℕ} (t : F) (ht : t ≠ 0) :
    paperCtAlternantPolynomial (n := n) t = paperCtFactorProduct t := by
  apply paper_normalize_scalar_from_lowest_coeff (n := n) (d := n * (n - 1) / 2)
    (paperCtFactorProduct (n := n) t) (paperCtAlternantPolynomial t)
    (paper_ct_full_factor_product_dvd t ht)
  · intro hz
    have hcoeff := paper_ct_factor_scale_lowest_coeff (n := n) t
    rw [hz] at hcoeff
    simp at hcoeff
    exact paper_pair_product_ne_zero (F := F) (n := n) hcoeff.symm
  · intro hz
    have hcoeff := paper_ct_scale_lowest_coeff (n := n) t
    rw [hz] at hcoeff
    simp at hcoeff
    have hD := paper_descending_vandermonde_eq_pair_product (F := F) (n := n)
    exact paper_pair_product_ne_zero (F := F) (n := n) (hD.symm ▸ hcoeff.symm)
  · rw [paper_ct_factor_product_totalDegree_eq t ht]
    exact paper_ct_alternant_totalDegree_le t
  · exact paper_pair_product_ne_zero (F := F) (n := n)
  · exact paper_ct_factor_scale_lowest_coeff (n := n) t
  · simpa only [paper_descending_vandermonde_eq_pair_product] using
      paper_ct_scale_lowest_coeff (n := n) t

theorem paper_bminus_factorization_by_lowest_part {n : ℕ} (τ : F) (hτ : τ ≠ 0) :
    paperBminusAlternantPolynomial (n := n) τ = paperBminusFactorProduct τ := by
  apply paper_normalize_scalar_from_lowest_coeff (n := n) (d := n * (n - 1) / 2)
    (paperBminusFactorProduct (n := n) τ) (paperBminusAlternantPolynomial τ)
    (paper_bminus_full_factor_product_dvd τ hτ)
  · intro hz
    have hcoeff := paper_bminus_factor_scale_lowest_coeff (n := n) τ
    rw [hz] at hcoeff
    simp at hcoeff
    exact paper_pair_product_ne_zero (F := F) (n := n) hcoeff.symm
  · intro hz
    have hcoeff := paper_bminus_scale_lowest_coeff (n := n) τ
    rw [hz] at hcoeff
    simp at hcoeff
    have hD := paper_descending_vandermonde_eq_pair_product (F := F) (n := n)
    exact paper_pair_product_ne_zero (F := F) (n := n) (hD.symm ▸ hcoeff.symm)
  · rw [paper_bminus_factor_product_totalDegree_eq τ hτ]
    exact paper_bminus_alternant_totalDegree_le τ
  · exact paper_pair_product_ne_zero (F := F) (n := n)
  · exact paper_bminus_factor_scale_lowest_coeff (n := n) τ
  · simpa only [paper_descending_vandermonde_eq_pair_product] using
      paper_bminus_scale_lowest_coeff (n := n) τ

theorem paper_basic_factorization_zero {n : ℕ} :
    paperBasicAlternantPolynomial (n := n) (0 : F) = paperBasicFactorProduct 0 := by
  rw [paper_basic_factor_product_eq_Nt]
  have hdet : paperBasicAlternantPolynomial (n := n) (0 : F) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X (R := F) a : MvPolynomial (Fin n) F) ^
          (n - (r.val + 1))).det := by
    classical
    apply congrArg Matrix.det
    ext a r
    by_cases hr : r.val = 0
    · simp [fColumn, hr]
    · simp [fColumn, hr]
  rw [hdet, paper_descending_vandermonde_eq_pair_product]
  simp [Nt, paperAlternantPairIndex, Fintype.prod_sigma]
  rfl

theorem paper_ct_factorization_zero {n : ℕ} :
    paperCtAlternantPolynomial (n := n) (0 : F) = paperCtFactorProduct 0 := by
  rw [paper_ct_factor_product_eq]
  have hdet : paperCtAlternantPolynomial (n := n) (0 : F) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X (R := F) a : MvPolynomial (Fin n) F) ^
          (n - (r.val + 1))).det := by
    simp [paperCtAlternantPolynomial, ctAlternantColumn]
  rw [hdet, paper_descending_vandermonde_eq_pair_product]
  simp [Nt, paperAlternantPairIndex, Fintype.prod_sigma]
  rfl

theorem paper_bminus_factorization_zero {n : ℕ} :
    paperBminusAlternantPolynomial (n := n) (0 : F) = paperBminusFactorProduct 0 := by
  rw [paper_bminus_factor_product_eq]
  have hdet : paperBminusAlternantPolynomial (n := n) (0 : F) =
      (Matrix.of fun a r : Fin n =>
        (MvPolynomial.X (R := F) a : MvPolynomial (Fin n) F) ^
          (n - (r.val + 1))).det := by
    simp [paperBminusAlternantPolynomial, bminusAlternantColumn]
  rw [hdet, paper_descending_vandermonde_eq_pair_product]
  simp [Nt, paperAlternantPairIndex, Fintype.prod_sigma]
  rfl

end
end AffineDualJT
