import AffineDualJT.ReducedNumerators
import AffineDualJT.FiniteColumnEvaluation

/-! # Proposition 2.2, the `B+` finite determinant -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem reducedBplus_det_sum (x : Fin n → Fˣ) (t : F) (k : ℕ)
    (hDelta : DeltaPlus x≠0) :
    RedBplus x t k =
      (∑ η : Fin n → Bool, (basicWeightedMatrix (invertedVariables x η) t k).det)/
        DeltaPlus x := by
  classical
  rw [RedBplus,reducedWeyl,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro η _
  have h := basicWeightedMatrix_plus_ratio (invertedVariables x η) t k
    (by rwa [deltaPlus_invertedVariables])
  rw [deltaPlus_invertedVariables] at h
  simpa only [coe_invertedVariables,mul_one] using h.symm

theorem finite_bplus_ratio_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaPlus x≠0) :
    RedBplus x t k = (PhiPlus (k := k) x*VBplus (n := n) (k := k) t).det/DeltaPlus x := by
  classical
  rw [reducedBplus_det_sum x t k hDelta]
  congr 1
  let g : Fin n → Bool → Fin n → F := fun a b r =>
    (if b=true then (x a : F)⁻¹ else (x a : F))^(-((n:ℤ)+(k:ℤ)-1))*
      fColumn t r (if b=true then (x a : F)⁻¹ else (x a : F))
  have h := det_bool_rows g
  have hfold : (Matrix.of fun a r => g a false r+g a true r) =
      PhiPlus (k := k) x*VBplus (n := n) (k := k) t := by
    ext a r
    simpa only [g,Matrix.of_apply,Bool.false_eq_true,ite_false,ite_true] using
      weighted_fColumn_plus_fold_all_width (k := k) x t a r
  rw [hfold] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro η _
  apply congrArg Matrix.det
  ext a r
  simp only [basicWeightedMatrix,Matrix.of_apply,coe_invertedVariables,g]

theorem finite_bplus_ratio (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaPlus x≠0) :
    RedBplus x t k = (PhiPlus (k := k) x*VBplus (n := n) (k := k) t).det/DeltaPlus x := finite_bplus_ratio_all_width (k := k) x t hDelta

end
end AffineDualJT
