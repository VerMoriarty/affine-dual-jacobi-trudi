import AffineDualJT.FiniteColumns
import AffineDualJT.ClassicalTransfer

/-!
# The seven finite-column specializations at zero parameter

Every column in Table 1 becomes the coordinate vector in row `k+r`,
as used in Corollary 6.2. Positive width is required for the `Plus` folding,
whose bracket at index one is doubled.
-/
open Matrix
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
private theorem leadingC (p : Fin (n+k)) (r : Fin n) :
    bracketC ((k:ℤ)+paperIndex r) p = classicalV (F:=F) p r := by
  have hp := paperIndex_pos p
  have hr := paperIndex_pos r
  have hneg : (k:ℤ)+paperIndex r ≠ -paperIndex p := by omega
  have he : (k:ℤ)+paperIndex r = paperIndex p ↔
      p = (⟨k+r.val, by omega⟩ : Fin (n+k)) := by
    rw [Fin.ext_iff]
    simp only [paperIndex]
    omega
  change (if (k:ℤ)+paperIndex r = paperIndex p then 1 else
    if (k:ℤ)+paperIndex r = -paperIndex p then -1 else 0) =
      if p = (⟨k+r.val, by omega⟩ : Fin (n+k)) then 1 else 0
  simp only [he, hneg, ite_false]
private theorem leadingB (p : Fin (n+k)) (r : Fin n) :
    bracketB ((k:ℤ)+paperIndex r) p = classicalV (F:=F) p r := by
  have hp := paperIndex_pos p
  have hr := paperIndex_pos r
  have hneg : 1-((k:ℤ)+paperIndex r) ≠ paperIndex p := by omega
  have he : (k:ℤ)+paperIndex r = paperIndex p ↔
      p = (⟨k+r.val, by omega⟩ : Fin (n+k)) := by
    rw [Fin.ext_iff]
    simp only [paperIndex]
    omega
  change (if (k:ℤ)+paperIndex r = paperIndex p then 1 else
    if 1-((k:ℤ)+paperIndex r) = paperIndex p then -1 else 0) =
      if p = (⟨k+r.val, by omega⟩ : Fin (n+k)) then 1 else 0
  simp only [he, hneg, ite_false]
private theorem leadingPlus (hk : 0 < k) (p : Fin (n+k)) (r : Fin n) :
    bracketPlus ((k:ℤ)+paperIndex r) p = classicalV (F:=F) p r := by
  have hp := paperIndex_pos p
  have hr := paperIndex_pos r
  have hfixed : (k:ℤ)+paperIndex r ≠ 1 := by omega
  have hneg : 2-((k:ℤ)+paperIndex r) ≠ paperIndex p := by omega
  have he : (k:ℤ)+paperIndex r = paperIndex p ↔
      p = (⟨k+r.val, by omega⟩ : Fin (n+k)) := by
    rw [Fin.ext_iff]
    simp only [paperIndex]
    omega
  change (if (k:ℤ)+paperIndex r = 1 then _ else
    if (k:ℤ)+paperIndex r = paperIndex p then 1 else
    if 2-((k:ℤ)+paperIndex r) = paperIndex p then 1 else 0) =
      if p = (⟨k+r.val, by omega⟩ : Fin (n+k)) then 1 else 0
  simp only [he, hneg, hfixed, ite_false]

theorem VC0_zero : VC0 (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  by_cases hr : r.val = 0
  · simp only [VC0, uC, ite_eq_left hr]
    have he : paperIndex r = 1 := by simp [paperIndex, hr]
    rw [← he]
    exact leadingC p r
  · simp only [VC0, uC, ite_eq_right hr, zero_pow hr, zero_mul, add_zero]
    exact leadingC p r

theorem VCt_zero : VCt (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  simp only [VCt, zero_pow (by omega : r.val+1 ≠ 0), zero_mul, sub_zero]
  exact leadingC p r

theorem VBC_zero : VBC (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  simp only [VBC, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, add_zero]
  exact congrFun (congrFun (VC0_zero (F:=F) (n:=n) (k:=k)) p) r

theorem VB0_zero : VB0 (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  by_cases hr : r.val = 0
  · simp only [VB0, uB, ite_eq_left hr]
    have he : paperIndex r = 1 := by simp [paperIndex, hr]
    rw [← he]
    exact leadingB p r
  · simp only [VB0, uB, ite_eq_right hr, zero_pow hr, zero_mul, add_zero]
    exact leadingB p r

theorem VBminus_zero : VBminus (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  simp only [VBminus, zero_pow (by omega : 2*r.val+1 ≠ 0), zero_mul, add_zero]
  exact leadingB p r

theorem VBplus_zero (hk : 0 < k) : VBplus (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  by_cases hr : r.val = 0
  · simp only [VBplus, uPlus, ite_eq_left hr]
    have he : paperIndex r = 1 := by simp [paperIndex, hr]
    rw [← he]
    exact leadingPlus hk p r
  · simp only [VBplus, uPlus, ite_eq_right hr, zero_pow hr, zero_mul, add_zero]
    exact leadingPlus hk p r

theorem VBt_zero : VBt (n:=n) (k:=k) (0:F) = classicalV := by
  ext p r
  simp only [VBt, zero_mul, sub_zero]
  exact congrFun (congrFun (VB0_zero (F:=F) (n:=n) (k:=k)) p) r
end
end AffineDualJT
