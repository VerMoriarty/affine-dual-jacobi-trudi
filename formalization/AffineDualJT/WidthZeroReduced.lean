import AffineDualJT.FiniteCB
import AffineDualJT.FiniteBplus
import AffineDualJT.WidthZeroColumns

/-! # Zero-width reduced Weyl sums via triangular column determinants -/
namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

theorem reduced_C0_width_zero (x : Fin n → Fˣ) (t : F) (hDelta : DeltaC x ≠ 0) :
    RedC0 x t 0 = 1 := by
  have hr := finite_c0_ratio_all_width (k := 0) x t hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VC0_det]
  change DeltaC x * 1 / DeltaC x = 1
  rw [mul_one, div_self hDelta]

theorem reduced_Ct_width_zero (x : Fin n → Fˣ) (t : F) (hDelta : DeltaC x ≠ 0) :
    RedCt x t 0 = ExternalHL.pochhammer n (-t) t := by
  have hr := finite_ct_ratio_all_width (k := 0) x t hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VCt_det]
  change DeltaC x * ExternalHL.pochhammer n (-t) t / DeltaC x = _
  exact mul_div_cancel_left₀ _ hDelta

theorem reduced_BC_width_zero (x : Fin n → Fˣ) (τ : F) (hDelta : DeltaC x ≠ 0) :
    RedBC x τ 0 = 1 := by
  have hr := finite_bc_ratio_all_width (k := 0) x τ hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VBC_det]
  change DeltaC x * 1 / DeltaC x = 1
  rw [mul_one, div_self hDelta]

theorem reduced_B0_width_zero (x : Fin n → Fˣ) (t : F) (hDelta : DeltaB x ≠ 0) :
    RedB0 x t 0 = 1 := by
  have hr := finite_b0_ratio_all_width (k := 0) x t hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VB0_det]
  change DeltaB x * 1 / DeltaB x = 1
  rw [mul_one, div_self hDelta]

theorem reduced_Bminus_width_zero (x : Fin n → Fˣ) (τ : F) (hDelta : DeltaB x ≠ 0) :
    RedBminus x τ 0 = ExternalHL.pochhammer n τ (τ^2) := by
  have hr := finite_bminus_ratio_all_width (k := 0) x τ hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VBminus_det]
  change DeltaB x * ExternalHL.pochhammer n τ (τ^2) / DeltaB x = _
  exact mul_div_cancel_left₀ _ hDelta

theorem reduced_Bplus_width_zero (x : Fin n → Fˣ) (t : F) (hDelta : DeltaPlus x ≠ 0) :
    RedBplus x t 0 = ExternalHL.pochhammer n (-1) t := by
  have hr := finite_bplus_ratio_all_width (k := 0) x t hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VBplus_det]
  change DeltaPlus x * ExternalHL.pochhammer n (-1) t / DeltaPlus x = _
  exact mul_div_cancel_left₀ _ hDelta

theorem reduced_Bt_width_zero (x : Fin n → Fˣ) (t : F) (hDelta : DeltaB x ≠ 0) :
    RedBt x t 0 = ExternalHL.pochhammer n (-t) t := by
  have hr := finite_bt_ratio_all_width (k := 0) x t hDelta
  refine hr.trans ?_
  rw [Matrix.det_mul, width_zero_VBt_det]
  change DeltaB x * ExternalHL.pochhammer n (-t) t / DeltaB x = _
  exact mul_div_cancel_left₀ _ hDelta

end
end AffineDualJT
