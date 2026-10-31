import AffineDualJT.FiniteWeyl
import AffineDualJT.ComplementaryMinors
import AffineDualJT.CoefficientMinors
import AffineDualJT.GeneratingFunctions
import AffineDualJT.FiniteUnfolding

/-! # Three coefficient kernels (§3.2, Lemma 3.2). -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Lemma32
variable {F : Type*} [Field F]
variable {n k : ℕ}

private theorem neg_zpow (x : F) (m : ℤ) : (-x)^m = (-1:F)^m * x^m := by
  rw [neg_eq_neg_one_mul, mul_zpow]
private theorem negOne_zpow_neg (m : ℤ) : (-1:F)^(-m) = (-1:F)^m := by
  simp only [← Int.cast_negOnePow F, Int.negOnePow_neg]
private theorem negOne_zpow_one_sub (m : ℤ) : (-1:F)^(1-m) = -(-1:F)^m := by
  simp only [← Int.cast_negOnePow F, Int.negOnePow_sub]
  norm_num
private theorem negOne_zpow_two_sub (m : ℤ) : (-1:F)^(2-m) = (-1:F)^m := by
  simp only [← Int.cast_negOnePow F, Int.negOnePow_sub]
  norm_num

/-- Lemma 3.2: `Φ^C D^C=0`. -/
theorem lemma_3_2_PhiC_DC (x : Fin n → Fˣ) :
    PhiC (k:=k) x * DC (k:=k) (classicalCoefficients x) = 0 := by
  ext a i
  have hx : -(x a : F) ≠ 0 := neg_ne_zero.mpr (Units.ne_zero _)
  have h := lambda_generating x i (-(x a : F)) hx
  rw [dotE_eval_neg_variable, mul_zero, zero_mul] at h
  rw [unfold_odd (n+k) (lambdaKernel (classicalCoefficients x) i)
    (fun m => (-(x a : F))^m) (lambdaKernel_zero _ i) (lambdaKernel_neg _ i)
    (fun m hm => lambdaKernel_zero_of_gt _ i m (by simpa using hm))] at h
  simp only [Matrix.zero_apply, mul_apply]
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_zpow (x a : F), neg_zpow (x a : F)]
  simp only [PhiC, DC, phi, rowSign_eq_zpow, negOne_zpow_neg]
  ring

/-- Lemma 3.2: `Φ^B D^B=0`. -/
theorem lemma_3_2_PhiB_DB (x : Fin n → Fˣ) :
    PhiB (k:=k) x * DB (k:=k) (classicalCoefficients x) = 0 := by
  ext a i
  have hx : -(x a : F) ≠ 0 := neg_ne_zero.mpr (Units.ne_zero _)
  have h := h_generating x i (-(x a : F)) hx
  rw [dotE_eval_neg_variable, mul_zero, zero_mul] at h
  rw [unfold_center_one (n+k) (hKernel (classicalCoefficients x) i)
    (fun m => (-(x a : F))^m) (hKernel_reflect _ i)
    (fun m hm => hKernel_zero_of_gt _ i m (by simpa using hm))] at h
  simp only [Matrix.zero_apply, mul_apply]
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_zpow (x a : F), neg_zpow (x a : F)]
  simp only [PhiB, DB, psi, rowSign_eq_zpow, negOne_zpow_one_sub]
  ring

/-- Lemma 3.2: `Φ^+ D^+=0`. -/
theorem lemma_3_2_PhiPlus_DPlus (x : Fin n → Fˣ) :
    PhiPlus (k:=k) x * DPlus (k:=k) (classicalCoefficients x) = 0 := by
  ext a i
  have hL : 0 < n+k := by have := i.isLt; omega
  have hx : (x a : F) ≠ 0 := Units.ne_zero _
  have h := hPlus_generating x i (-(x a : F)) (neg_ne_zero.mpr hx)
  rw [dotE_eval_neg_variable, mul_zero, zero_mul] at h
  rw [unfold_center_two (n+k) hL (hPlusKernel (classicalCoefficients x) i)
    (fun m => (-(x a : F))^m) (hPlusKernel_reflect _ i)
    (fun m hm => hPlusKernel_zero_of_gt _ i m (by simpa using hm))] at h
  simp only [Matrix.zero_apply]
  apply (mul_eq_zero.mp (show (PhiPlus (k:=k) x * DPlus (k:=k) (classicalCoefficients x)) a i *
      (x a : F) = 0 from ?_)).resolve_right hx
  rw [mul_apply, Finset.sum_mul]
  convert h using 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [PhiPlus, DPlus]
  by_cases hz : p.val = 0
  · simp [hz, paperIndex, rowSign]
  · rw [ite_eq_right hz, ite_eq_right hz, rowSign_eq_zpow]
    rw [neg_zpow (x a : F), neg_zpow (x a : F)]
    simp only [Cfun, negOne_zpow_two_sub]
    have h₁ : (x a : F)^(p.val:ℤ) * (x a : F) = (x a : F)^(paperIndex p) := by
      rw [paperIndex, zpow_add₀ hx, zpow_one]
    have h₂ : (x a : F)^(-(p.val:ℤ)) * (x a : F) = (x a : F)^(2-paperIndex p) := by
      rw [show 2-paperIndex p = -(p.val:ℤ)+1 by simp [paperIndex]; ring,
        zpow_add₀ hx, zpow_one]
    calc
      _ = (-1:F)^(paperIndex p) * hPlusKernel (classicalCoefficients x) i (paperIndex p) *
          ((x a : F)^(p.val:ℤ)*(x a : F)+(x a : F)^(-(p.val:ℤ))*(x a : F)) := by ring
      _ = _ := by rw [h₁, h₂]; ring

end Lemma32
end
end AffineDualJT
