import AffineDualJT.CoefficientMatrices

/-!
# Coefficient normalization minors, Lemma 3.2

Palindromicity identifies the tails with upper triangular coefficient
matrices. The diagonals are the row signs, except that the first `DPlus`
diagonal is doubled. Their product is `ζ=(-1)^(nk)ω`, as in the paper.
-/
open Matrix
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
private theorem lambda_tail_entry (c : CoeffSystem F n) (r i : Fin k) :
    lambdaKernel c i ((n:ℤ)+paperIndex r) = c.eDot (paperIndex i-paperIndex r) := by
  have hi := paperIndex_pos i
  have hr := paperIndex_pos r
  unfold lambdaKernel
  rw [c.eDot_zero_of_gt ((n:ℤ)+paperIndex i+((n:ℤ)+paperIndex r)) (by omega), sub_zero,
    ← c.eDot_pal]
  congr 1
  ring
private theorem h_tail_entry (c : CoeffSystem F n) (r i : Fin k) :
    hKernel c i ((n:ℤ)+paperIndex r) = c.eDot (paperIndex i-paperIndex r) := by
  have hi := paperIndex_pos i
  have hr := paperIndex_pos r
  unfold hKernel
  rw [c.eDot_zero_of_gt ((n:ℤ)+paperIndex i+((n:ℤ)+paperIndex r)-1) (by omega), add_zero,
    ← c.eDot_pal]
  congr 1
  ring
private theorem hPlus_tail_entry (c : CoeffSystem F n) (r i : Fin k) :
    hPlusKernel c i ((n:ℤ)+paperIndex r) = c.eDot (paperIndex i-paperIndex r) +
      if i.val = 0 ∧ r.val = 0 then c.eDot 0 else 0 := by
  have hi := paperIndex_pos i
  have hr := paperIndex_pos r
  unfold hPlusKernel
  have hp : c.eDot ((n:ℤ)-paperIndex i+((n:ℤ)+paperIndex r)) =
      c.eDot (paperIndex i-paperIndex r) := by
    rw [← c.eDot_pal]
    congr 1
    ring
  rw [hp]
  congr 1
  by_cases h : i.val = 0 ∧ r.val = 0
  · rw [ite_eq_left h, show (n:ℤ)+paperIndex i+((n:ℤ)+paperIndex r)-2 = 2*(n:ℤ) by
      simp [paperIndex,h.1,h.2]; ring]
    simpa using c.eDot_pal 0
  · rw [ite_eq_right h, c.eDot_zero_of_gt _ (by simp only [paperIndex]; omega)]
/-- The paper's diagonal sign product `ζ=(-1)^(nk)ω`. -/
theorem prod_tail_rowSign :
    (∏ i : Fin k, (-1:F)^(n+i.val+1)) = zetaSign F n k := by
  have hs : (∑ i : Fin k, (i.val+1)) = k*(k+1)/2 := by
    have hh := Finset.sum_range_id_mul_two k
    change (∑ i : Fin k, (fun i : ℕ => i+1) i.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1) k, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    have he : ((∑ i ∈ Finset.range k, i)+k)*2 = k*(k+1) := by
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel] at hh; nlinarith
    rw [← he, Nat.mul_div_cancel _ (by norm_num)]
  rw [Finset.prod_pow_eq_pow_sum]
  have he : (∑ i : Fin k, (n+i.val+1)) = n*k+k*(k+1)/2 := by
    simp_rw [show ∀ i : Fin k, n+i.val+1 = n+(i.val+1) by intro i; omega]
    rw [Finset.sum_add_distrib, hs]
    simp [mul_comm]
  rw [he, pow_add]
  rfl

/-- Lemma 3.2: `det D^C_J = ζ`. -/
theorem lemma_3_2_minor_DC (x : Fin n → Fˣ) :
    (tailRowsAfterN (DC (k:=k) (classicalCoefficients x))).det = zetaSign F n k := by
  rw [det_of_isUpperTriangular]
  · convert prod_tail_rowSign (F:=F) (n:=n) (k:=k) using 1
    apply Finset.prod_congr rfl
    intro r hr
    change rowSign ⟨n+r.val, by omega⟩ * lambdaKernel (classicalCoefficients x) r
      ((n:ℤ)+paperIndex r) = (-1:F)^(n+r.val+1)
    rw [lambda_tail_entry, sub_self, classicalCoefficients_eDot_zero, mul_one]
    rfl
  · intro r i hri
    simp only [id_eq, Fin.lt_def] at hri
    change rowSign ⟨n+r.val, by omega⟩ * lambdaKernel (classicalCoefficients x) i
      ((n:ℤ)+paperIndex r) = 0
    rw [lambda_tail_entry, (classicalCoefficients x).eDot_zero_of_neg _
      (by simp only [paperIndex]; omega), mul_zero]
end
end AffineDualJT

namespace AffineDualJT
open Matrix
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
/-- Lemma 3.2: `det D^B_J = ζ`. -/
theorem lemma_3_2_minor_DB (x : Fin n → Fˣ) :
    (tailRowsAfterN (DB (k:=k) (classicalCoefficients x))).det = zetaSign F n k := by
  rw [det_of_isUpperTriangular]
  · convert prod_tail_rowSign (F:=F) (n:=n) (k:=k) using 1
    apply Finset.prod_congr rfl
    intro r hr
    change rowSign ⟨n+r.val, by omega⟩ * hKernel (classicalCoefficients x) r
      ((n:ℤ)+paperIndex r) = (-1:F)^(n+r.val+1)
    rw [h_tail_entry, sub_self, classicalCoefficients_eDot_zero, mul_one]
    rfl
  · intro r i hri
    simp only [id_eq, Fin.lt_def] at hri
    change rowSign ⟨n+r.val, by omega⟩ * hKernel (classicalCoefficients x) i
      ((n:ℤ)+paperIndex r) = 0
    rw [h_tail_entry, (classicalCoefficients x).eDot_zero_of_neg _
      (by simp only [paperIndex]; omega), mul_zero]

/-- Lemma 3.2: `det D^+_J = 2ζ`, with positive width. -/
theorem lemma_3_2_minor_DPlus (x : Fin n → Fˣ) (hk : 0 < k) :
    (tailRowsAfterN (DPlus (k:=k) (classicalCoefficients x))).det = 2*zetaSign F n k := by
  rw [det_of_isUpperTriangular]
  · have he : ∀ r : Fin k,
        tailRowsAfterN (DPlus (k:=k) (classicalCoefficients x)) r r =
          (-1:F)^(n+r.val+1) * (if r.val = 0 then 2 else 1) := by
      intro r
      change rowSign ⟨n+r.val, by omega⟩ * hPlusKernel (classicalCoefficients x) r
        ((n:ℤ)+paperIndex r) = _
      rw [hPlus_tail_entry, sub_self, classicalCoefficients_eDot_zero]
      by_cases hr : r.val = 0 <;> simp [rowSign, hr]
      ring
    simp_rw [he]
    rw [Finset.prod_mul_distrib, prod_tail_rowSign]
    have hp : (∏ r : Fin k, (if r.val = 0 then (2:F) else 1)) = 2 := by
      have hv : ∀ r : Fin k, r.val = 0 ↔ r = ⟨0,hk⟩ := by
        intro r
        exact (Fin.ext_iff (a := r) (b := ⟨0,hk⟩)).symm
      simp_rw [hv]
      simp
    rw [hp, mul_comm]
  · intro r i hri
    simp only [id_eq, Fin.lt_def] at hri
    change rowSign ⟨n+r.val, by omega⟩ * hPlusKernel (classicalCoefficients x) i
      ((n:ℤ)+paperIndex r) = 0
    rw [hPlus_tail_entry, (classicalCoefficients x).eDot_zero_of_neg _
      (by simp only [paperIndex]; omega), ite_eq_right (by omega)]
    simp
end
end AffineDualJT
