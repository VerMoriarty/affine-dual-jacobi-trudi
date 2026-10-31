import AffineDualJT.WeylMatrices
import AffineDualJT.WeylPolynomials

/-!
# The three Weyl denominator products, source.tex (2.6)

This follows the paper's Vandermonde proof in `z + z⁻¹`, with explicit
monic polynomial columns and an explicit count of each variable's exponent.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix Polynomial Finset
noncomputable section

theorem prod_pair_endpoints {M : Type*} [CommMonoid M] {n : ℕ}
    (v : Fin n → M) :
    (∏ a : Fin n, ∏ b ∈ Ioi a, v a * v b) = ∏ a : Fin n, v a ^ (n - 1) := by
  classical
  simp_rw [prod_mul_distrib]
  have hswap : (∏ a : Fin n, ∏ b ∈ Ioi a, v b) =
      ∏ b : Fin n, ∏ a ∈ Iio b, v b := by
    apply prod_comm'
    simp
  rw [hswap, ← prod_mul_distrib]
  apply prod_congr rfl
  intro a _
  simp only [prod_const, Fin.card_Ioi, Fin.card_Iio, ← pow_add]
  congr 1
  omega

variable {F : Type*} [Field F] {n : ℕ}

theorem deltaC_vandermonde (x : Fin n → Fˣ) :
    DeltaC x = (∏ a : Fin n, ((x a : F) - (x a : F)⁻¹)) *
      (vandermonde fun a => (x a : F) + (x a : F)⁻¹).det := by
  classical
  have hv := det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun a => (x a : F) + (x a : F)⁻¹)
    (fun r : Fin n => weylPolyC (F := F) r.val)
    (fun r => (weylPolyC_monic_degree r.val).2)
    (fun r => (weylPolyC_monic_degree r.val).1)
  rw [hv]
  convert det_mul_column (fun a => (x a : F) - (x a : F)⁻¹)
    (Matrix.of fun a r : Fin n => (weylPolyC (F := F) r.val).eval
      ((x a : F) + (x a : F)⁻¹)) using 1
  apply congrArg Matrix.det
  ext a r
  exact (weylPolyC_eval (x a : F) (Units.ne_zero _) r.val).symm

theorem deltaB_vandermonde (x : Fin n → Fˣ) :
    DeltaB x = (∏ a : Fin n, ((x a : F) - 1)) *
      (vandermonde fun a => (x a : F) + (x a : F)⁻¹).det := by
  classical
  have hv := det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun a => (x a : F) + (x a : F)⁻¹)
    (fun r : Fin n => weylPolyB (F := F) r.val)
    (fun r => (weylPolyB_monic_degree r.val).2)
    (fun r => (weylPolyB_monic_degree r.val).1)
  rw [hv]
  convert det_mul_column (fun a => (x a : F) - 1)
    (Matrix.of fun a r : Fin n => (weylPolyB (F := F) r.val).eval
      ((x a : F) + (x a : F)⁻¹)) using 1
  apply congrArg Matrix.det
  ext a r
  simpa [DeltaB, psi, paperIndex] using
    (weylPolyB_eval (x a : F) (Units.ne_zero _) r.val).symm

theorem deltaPlus_vandermonde (x : Fin n → Fˣ) :
    DeltaPlus x = (vandermonde fun a => (x a : F) + (x a : F)⁻¹).det := by
  classical
  have hv := det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun a => (x a : F) + (x a : F)⁻¹)
    (fun r : Fin n => weylPolyPlus (F := F) r.val)
    (fun r => (weylPolyPlus_monic_degree r.val).2)
    (fun r => (weylPolyPlus_monic_degree r.val).1)
  rw [hv]
  apply congrArg Matrix.det
  ext a r
  exact (weylPolyPlus_eval (x a : F) (Units.ne_zero _) r.val).symm

theorem vandermonde_add_inv_product (x : Fin n → Fˣ) :
    (vandermonde fun a => (x a : F) + (x a : F)⁻¹).det =
      (∏ a : Fin n, ((x a : F)⁻¹) ^ (n - 1)) * Nt 1 (fun a => (x a : F)) := by
  classical
  rw [det_vandermonde]
  have hdiff (a b : Fin n) :
      (x b : F) + (x b : F)⁻¹ - ((x a : F) + (x a : F)⁻¹) =
        ((x a : F)⁻¹ * (x b : F)⁻¹) *
          (((x a : F) - (x b : F)) * (1 - (x a : F) * (x b : F))) := by
    field_simp
    ring
  calc
    (∏ a : Fin n, ∏ b ∈ Ioi a,
        ((x b : F) + (x b : F)⁻¹ - ((x a : F) + (x a : F)⁻¹))) =
      (∏ a : Fin n, ∏ b ∈ Ioi a, (x a : F)⁻¹ * (x b : F)⁻¹) *
        (∏ a : Fin n, ∏ b ∈ Ioi a,
          ((x a : F) - (x b : F)) * (1 - (x a : F) * (x b : F))) := by
      simp_rw [hdiff, prod_mul_distrib]
    _ = _ := by
      rw [prod_pair_endpoints]
      congr 1
      unfold Nt
      apply prod_congr rfl
      intro a _
      simpa only [one_mul] using
        prod_subtype (Ioi a) (fun b => by simp) (fun b =>
          ((x a : F) - (x b : F)) * (1 - (x a : F) * (x b : F)))

/-- Equation (2.6), the `C` denominator product. -/
theorem deltaC_product (x : Fin n → Fˣ) :
    DeltaC x = (-1 : F)^n *
      (∏ a : Fin n, ((x a : F) ^ (-(n : ℤ))) * (1 - (x a : F)^2)) *
      Nt 1 (fun a => (x a : F)) := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [show DeltaC x = 1 from Matrix.det_isEmpty]
    simp [Nt]
  rw [deltaC_vandermonde, vandermonde_add_inv_product, ← mul_assoc, ← prod_mul_distrib]
  have hrow (a : Fin n) :
      ((x a : F) - (x a : F)⁻¹) * ((x a : F)⁻¹) ^ (n - 1) =
        (-1 : F) * ((x a : F) ^ (-(n : ℤ)) * (1 - (x a : F)^2)) := by
    rw [inv_pow, ← zpow_natCast, ← _root_.zpow_neg,
      show -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 by omega,
      zpow_add₀ (Units.ne_zero _)]
    simp only [zpow_one]
    field_simp
    ring
  simp_rw [hrow]
  rw [prod_mul_distrib]
  simp

/-- Equation (2.6), the `B` denominator product. -/
theorem deltaB_product (x : Fin n → Fˣ) :
    DeltaB x = (-1 : F)^n *
      (∏ a : Fin n, ((x a : F) ^ (-(n : ℤ) + 1)) * (1 - (x a : F))) *
      Nt 1 (fun a => (x a : F)) := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [show DeltaB x = 1 from Matrix.det_isEmpty]
    simp [Nt]
  rw [deltaB_vandermonde, vandermonde_add_inv_product, ← mul_assoc, ← prod_mul_distrib]
  have hrow (a : Fin n) :
      ((x a : F) - 1) * ((x a : F)⁻¹) ^ (n - 1) =
        (-1 : F) * ((x a : F) ^ (-(n : ℤ) + 1) * (1 - (x a : F))) := by
    rw [inv_pow, ← zpow_natCast, ← _root_.zpow_neg,
      show -((n - 1 : ℕ) : ℤ) = -(n : ℤ) + 1 by omega]
    ring
  simp_rw [hrow]
  rw [prod_mul_distrib]
  simp

/-- Equation (2.6), the `+` denominator product, including its exceptional first column. -/
theorem deltaPlus_product (x : Fin n → Fˣ) :
    DeltaPlus x =
      (∏ a : Fin n, (x a : F) ^ (-(n : ℤ) + 1)) * Nt 1 (fun a => (x a : F)) := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [show DeltaPlus x = 1 from Matrix.det_isEmpty]
    simp [Nt]
  rw [deltaPlus_vandermonde, vandermonde_add_inv_product]
  congr 1
  apply prod_congr rfl
  intro a _
  rw [inv_pow, ← zpow_natCast, ← _root_.zpow_neg]
  congr 1
  omega

end
end AffineDualJT
