import AffineDualJT.AlternantMatrices
import AffineDualJT.AlternantPolynomials
import AffineDualJT.WeylDenominators

/-!
# Row factors for the reciprocal substitutions in Lemma 2.1

These factorizations establish the proportional-row step used in the
paper’s proof; the determinant identities are proved in `FiniteWeyl`.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix Polynomial Finset
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

theorem fColumn_row_factor (t z : F) (hz : z ≠ 0) (r : Fin n) :
    fColumn t r z = z^(n-1)*(alternantPolyBasic t r.val).eval (z⁻¹+t*z) := by
  by_cases hr : r.val = 0
  · simp [fColumn, alternantPolyBasic, hr]
  rw [fColumn, ite_eq_right hr, alternantPolyBasic_eval t z hz, ite_eq_right hr]
  have h₁ : z^(n-(r.val+1)) = z^(n-1)*z^(-(r.val:ℤ)) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  have h₂ : z^(n+r.val-1) = z^(n-1)*z^(r.val:ℤ) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  rw [h₁,h₂]
  ring

theorem ctAlternantColumn_row_factor (t z : F) (hz : z ≠ 0) (r : Fin n) :
    ctAlternantColumn t r z =
      (z^(n-1)*(1-t*z^2))*(alternantPolyCt t r.val).eval (z⁻¹+t*z) := by
  rw [mul_assoc, alternantPolyCt_eval t z hz]
  have h₁ : z^(n-(r.val+1)) = z^(n-1)*z^(-(r.val:ℤ)) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  have h₂ : z^(n+r.val+1) = z^(n-1)*z^((r.val:ℤ)+2) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  rw [ctAlternantColumn,h₁,h₂]
  ring

theorem bminusAlternantColumn_row_factor (τ z : F) (hz : z ≠ 0) (r : Fin n) :
    bminusAlternantColumn τ r z =
      (z^(n-1)*(1+τ*z))*(alternantPolyBminus τ r.val).eval (z⁻¹+τ^2*z) := by
  rw [mul_assoc, alternantPolyBminus_eval τ z hz]
  have h₁ : z^(n-(r.val+1)) = z^(n-1)*z^(-(r.val:ℤ)) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  have h₂ : z^(n+r.val) = z^(n-1)*z^((r.val:ℤ)+1) := by
    simp only [← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    have := r.isLt
    omega
  rw [bminusAlternantColumn,h₁,h₂]
  ring


end
end AffineDualJT
