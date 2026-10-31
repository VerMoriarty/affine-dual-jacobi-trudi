import AffineDualJT.ReducedNumerators

/-! # Finite inversion sums and row folding for Proposition 2.2 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

/-- Finite row multilinearity, with a coefficient on the inverted row. -/
theorem det_weighted_bool_rows (g : Fin n → Bool → Fin n → F) (μ : Fin n → F) :
    (Matrix.of fun a r => g a false r+μ a*g a true r).det =
      ∑ η : Fin n → Bool,
        (∏ a : Fin n, if η a=true then μ a else 1)*
          (Matrix.of fun a r => g a (η a) r).det := by
  classical
  have h := det_bool_rows (fun a b r => (if b=true then μ a else 1)*g a b r)
  simp only [Bool.false_eq_true,ite_false,ite_true,one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro η _
  exact det_mul_column _ _

/-- Clearing a denominator whose row inversion factor is inverse to `μ`. -/
theorem inversion_sum_ratio (x : Fin n → Fˣ)
    (D : (Fin n → Fˣ) → F) (hD : D x≠0)
    (g : F → Fin n → F) (ell μ : F → F)
    (hellμ : ∀ a, ell (x a : F)*μ (x a : F)=1)
    (hinv : ∀ η, D (invertedVariables x η)=
      (∏ a : Fin n, if η a=true then ell (x a : F) else 1)*D x) :
    (∑ η : Fin n → Bool,
      (Matrix.of fun a r => g (invertedVariables x η a : F) r).det /
        D (invertedVariables x η)) =
      (Matrix.of fun a r => g (x a : F) r+μ (x a : F)*g (x a : F)⁻¹ r).det/D x := by
  classical
  have hfold := det_weighted_bool_rows
    (fun a b r => g (if b=true then (x a : F)⁻¹ else (x a : F)) r)
    (fun a => μ (x a : F))
  simp only [Bool.false_eq_true,ite_false,ite_true] at hfold
  rw [hfold,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro η _
  have hp : (∏ a : Fin n, if η a=true then ell (x a : F) else 1)*
      (∏ a : Fin n, if η a=true then μ (x a : F) else 1)=1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro a _
    by_cases hη : η a=true
    · simp only [hη,ite_true,hellμ]
    · simp only [hη,Bool.false_eq_true,ite_false,one_mul]
  have hp0 := (mul_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero :
    (∏ a : Fin n, if η a=true then ell (x a : F) else 1)*
      (∏ a : Fin n, if η a=true then μ (x a : F) else 1)≠0)).1
  rw [hinv]
  simp only [coe_invertedVariables]
  apply (div_eq_div_iff (mul_ne_zero hp0 hD) hD).mpr
  linear_combination -(Matrix.of fun a r =>
    g (if η a=true then (x a : F)⁻¹ else (x a : F)) r).det*D x*hp

end
end AffineDualJT
