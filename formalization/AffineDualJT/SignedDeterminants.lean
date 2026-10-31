import AffineDualJT.BracketEvaluation

/-!
# Row inversion and finite inversion sums, source.tex §2.2

The three Weyl denominators acquire the row factors `-1`, `-z⁻¹`,
and `1`. Finite row multilinearity folds the `2^n` inversion choices.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

def invertedVariables (x : Fin n → Fˣ) (η : Fin n → Bool) (a : Fin n) : Fˣ :=
  if η a=true then (x a)⁻¹ else x a

@[simp] theorem coe_invertedVariables (x : Fin n → Fˣ) (η : Fin n → Bool) (a : Fin n) :
    (invertedVariables x η a : F) = if η a=true then (x a : F)⁻¹ else (x a : F) := by
  cases hη : η a <;> simp [invertedVariables,hη]

theorem phi_inv (z : F) (m : ℤ) : phi m z⁻¹ = -phi m z := by
  simp only [phi,_root_.inv_zpow,← _root_.zpow_neg,neg_neg]
  ring

theorem psi_inv (z : F) (hz : z≠0) (m : ℤ) : psi m z⁻¹ = -z⁻¹*psi m z := by
  have h₁ : z⁻¹*z^m=z^(m-1) := by
    calc
      _ = z^(-1+m) := by rw [zpow_add₀ hz,_root_.zpow_neg_one]
      _ = _ := by congr 1; ring
  have h₂ : z⁻¹*z^(1-m)=z^(-m) := by
    calc
      _ = z^(-1+(1-m)) := by rw [zpow_add₀ hz,_root_.zpow_neg_one]
      _ = _ := by congr 1; ring
  simp only [psi,_root_.inv_zpow,← _root_.zpow_neg,show -(1-m)=m-1 by ring]
  linear_combination h₁-h₂

theorem Cfun_inv (z : F) (m : ℤ) : Cfun m z⁻¹ = Cfun m z := by
  simp only [Cfun,_root_.inv_zpow,← _root_.zpow_neg,neg_neg]
  ring

theorem deltaC_invertedVariables (x : Fin n → Fˣ) (η : Fin n → Bool) :
    DeltaC (invertedVariables x η) =
      (∏ a : Fin n, (if η a=true then (-1:F) else 1))*DeltaC x := by
  classical
  unfold DeltaC
  convert det_mul_column (fun a => if η a=true then (-1:F) else 1)
    (Matrix.of fun a r : Fin n => phi (paperIndex r) (x a : F)) using 1
  · apply congrArg Matrix.det
    ext a r
    cases hη : η a <;> simp only [Matrix.of_apply,coe_invertedVariables,hη,Bool.false_eq_true,
      ite_false,ite_true,phi_inv,neg_one_mul,one_mul]
  · rfl

theorem deltaB_invertedVariables (x : Fin n → Fˣ) (η : Fin n → Bool) :
    DeltaB (invertedVariables x η) =
      (∏ a : Fin n, (if η a=true then -(x a : F)⁻¹ else 1))*DeltaB x := by
  classical
  unfold DeltaB
  convert det_mul_column (fun a => if η a=true then -(x a : F)⁻¹ else 1)
    (Matrix.of fun a r : Fin n => psi (paperIndex r) (x a : F)) using 1
  · apply congrArg Matrix.det
    ext a r
    cases hη : η a <;> simp only [Matrix.of_apply,coe_invertedVariables,hη,Bool.false_eq_true,
      ite_false,ite_true,psi_inv (x a : F) (Units.ne_zero (x a)),one_mul]
  · rfl

theorem deltaPlus_invertedVariables (x : Fin n → Fˣ) (η : Fin n → Bool) :
    DeltaPlus (invertedVariables x η) = DeltaPlus x := by
  apply congrArg Matrix.det
  ext a r
  cases hη : η a <;> simp only [coe_invertedVariables,hη,Bool.false_eq_true,
    ite_false,ite_true,Cfun_inv]

theorem deltaC_invertedVariables_ne_zero (x : Fin n → Fˣ) (η : Fin n → Bool)
    (hDelta : DeltaC x≠0) : DeltaC (invertedVariables x η)≠0 := by
  rw [deltaC_invertedVariables]
  apply mul_ne_zero _ hDelta
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  split_ifs <;> norm_num

theorem deltaB_invertedVariables_ne_zero (x : Fin n → Fˣ) (η : Fin n → Bool)
    (hDelta : DeltaB x≠0) : DeltaB (invertedVariables x η)≠0 := by
  rw [deltaB_invertedVariables]
  apply mul_ne_zero _ hDelta
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  split_ifs
  · exact neg_ne_zero.mpr (inv_ne_zero (Units.ne_zero _))
  · exact one_ne_zero

/-- Summing independently over inversion choices is finite row multilinearity. -/
theorem det_bool_rows (g : Fin n → Bool → Fin n → F) :
    (Matrix.of fun a r => g a false r+g a true r).det =
      ∑ η : Fin n → Bool, (Matrix.of fun a r => g a (η a) r).det := by
  classical
  have h := (detRowAlternating (R := F) (n := Fin n)).toMultilinearMap.map_sum g
  simp only [Fintype.sum_bool,add_comm] at h
  convert h using 1 <;> rfl

end
end AffineDualJT
