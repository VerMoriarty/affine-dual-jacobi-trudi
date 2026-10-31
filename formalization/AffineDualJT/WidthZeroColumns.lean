import AffineDualJT.FiniteColumnData
import AffineDualJT.HallLittlewoodWeyl

/-! # The triangular finite column matrices at width zero, source.tex §6.1 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

theorem width_zero_VC0_upper (t : F) : (VC0 (n := n) (k := 0) t).IsUpperTriangular := by
  intro p r hpr
  change r.val < p.val at hpr
  simp only [VC0, uC, bracketC, paperIndex, Nat.cast_zero, zero_add]
  split_ifs <;> simp_all [bracketC, paperIndex]
  all_goals split_ifs <;> first | omega | simp_all

theorem width_zero_VC0_diagonal (t : F) (r : Fin n) :
    VC0 (n := n) (k := 0) t r r = 1 := by
  simp only [VC0, uC, bracketC, paperIndex, Nat.cast_zero, zero_add]
  split_ifs <;> simp_all [bracketC, paperIndex]
  all_goals split_ifs <;> first | omega | simp_all

theorem width_zero_VC0_det (t : F) : (VC0 (n := n) (k := 0) t).det = 1 := by
  classical
  rw [det_of_isUpperTriangular (width_zero_VC0_upper t)]
  simp only [width_zero_VC0_diagonal, Finset.prod_const_one]

theorem width_zero_VCt_det (t : F) : (VCt (n := n) (k := 0) t).det =
    ExternalHL.pochhammer n (-t) t := by
  classical
  have ht : (VCt (n := n) (k := 0) t).IsUpperTriangular := by
    intro p r hpr
    change r.val < p.val at hpr
    simp only [VCt, bracketC, paperIndex, Nat.cast_zero, zero_add, zero_sub]
    split_ifs <;> first | omega | ring_nf
  rw [det_of_isUpperTriangular ht]
  clear ht
  have hd (r : Fin n) : VCt (n := n) (k := 0) t r r = 1 + t^(r.val+1) := by
    simp only [VCt, bracketC, paperIndex, Nat.cast_zero, zero_add, zero_sub]
    split_ifs <;> first | omega | ring_nf
  simp only [hd, ExternalHL.pochhammer]
  apply Finset.prod_congr rfl
  intro r _
  ring

theorem width_zero_uCTilde_zero (t : F) (p r : Fin n) (h : r ≤ p) :
    uCTilde (n := n) (k := 0) t r p = 0 := by
  change r.val ≤ p.val at h
  have hb (m : ℤ) (hlo : -(p.val : ℤ) ≤ m) (hhi : m ≤ (p.val : ℤ)) :
      bracketC (F := F) m p = 0 := by
    simp only [bracketC, paperIndex,
      show m ≠ (p.val : ℤ)+1 by omega,
      show m ≠ -((p.val : ℤ)+1) by omega, ite_false]
  by_cases hr0 : r.val = 0
  · simp only [uCTilde, hr0, ite_true, Nat.cast_zero]
    exact hb 0 (by omega) (by omega)
  · simp only [uCTilde, hr0, ite_false, Nat.cast_zero, zero_add]
    rw [hb (paperIndex r-1) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
      hb (1-paperIndex r) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
    ring

theorem width_zero_VBC_det (τ : F) : (VBC (n := n) (k := 0) τ).det = 1 := by
  classical
  have ht : (VBC (n := n) (k := 0) τ).IsUpperTriangular := by
    intro p r hpr
    change uC (n := n) (k := 0) (τ^2) r p +
      τ * uCTilde (n := n) (k := 0) (τ^2) r p = 0
    have hmain := width_zero_VC0_upper (n := n) (τ^2) hpr
    change uC (n := n) (k := 0) (τ^2) r p = 0 at hmain
    rw [hmain, width_zero_uCTilde_zero (τ^2) p r (le_of_lt hpr)]
    ring
  rw [det_of_isUpperTriangular ht]
  have hd (r : Fin n) : VBC (n := n) (k := 0) τ r r = 1 := by
    change uC (n := n) (k := 0) (τ^2) r r +
      τ * uCTilde (n := n) (k := 0) (τ^2) r r = 1
    have hmain := width_zero_VC0_diagonal (n := n) (τ^2) r
    change uC (n := n) (k := 0) (τ^2) r r = 1 at hmain
    rw [hmain, width_zero_uCTilde_zero (τ^2) r r le_rfl]
    ring
  simp only [hd, Finset.prod_const_one]

theorem width_zero_VB0_det (t : F) : (VB0 (n := n) (k := 0) t).det = 1 := by
  classical
  have ht : (VB0 (n := n) (k := 0) t).IsUpperTriangular := by
    intro p r hpr
    change r.val < p.val at hpr
    simp only [VB0, uB, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> simp_all [bracketB, paperIndex]
    all_goals split_ifs <;> first | omega | ring_nf
  rw [det_of_isUpperTriangular ht]
  clear ht
  have hd (r : Fin n) : VB0 (n := n) (k := 0) t r r = 1 := by
    simp only [VB0, uB, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> simp_all [bracketB, paperIndex]
    all_goals split_ifs <;> first | omega | ring_nf
  simp only [hd, Finset.prod_const_one]

theorem width_zero_VBminus_det (τ : F) : (VBminus (n := n) (k := 0) τ).det =
    ExternalHL.pochhammer n τ (τ^2) := by
  classical
  have ht : (VBminus (n := n) (k := 0) τ).IsUpperTriangular := by
    intro p r hpr
    change r.val < p.val at hpr
    simp only [VBminus, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> first | omega | ring_nf
  rw [det_of_isUpperTriangular ht]
  clear ht
  have hd (r : Fin n) : VBminus (n := n) (k := 0) τ r r = 1 - τ^(2*r.val+1) := by
    simp only [VBminus, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> first | omega | ring_nf
  simp only [hd, ExternalHL.pochhammer]
  apply Finset.prod_congr rfl
  intro r _
  rw [pow_add, pow_mul]
  ring

theorem width_zero_VBplus_det (t : F) : (VBplus (n := n) (k := 0) t).det =
    ExternalHL.pochhammer n (-1) t := by
  classical
  have ht : (VBplus (n := n) (k := 0) t).IsUpperTriangular := by
    intro p r hpr
    change r.val < p.val at hpr
    have hp0 : p.val ≠ 0 := by omega
    simp only [VBplus, uPlus, bracketPlus, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> (first | omega | simp_all [bracketPlus])
    all_goals first | omega | (split_ifs <;> first | omega | simp_all)
  rw [det_of_isUpperTriangular ht]
  clear ht
  have hd (r : Fin n) : VBplus (n := n) (k := 0) t r r = 1 + t^r.val := by
    simp only [VBplus, uPlus, bracketPlus, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> (first | omega | simp_all [bracketPlus])
    all_goals norm_num
  simp only [hd, ExternalHL.pochhammer, neg_one_mul, sub_neg_eq_add]
  rfl

theorem width_zero_VBt_det (t : F) : (VBt (n := n) (k := 0) t).det =
    ExternalHL.pochhammer n (-t) t := by
  classical
  have ht : (VBt (n := n) (k := 0) t).IsUpperTriangular := by
    intro p r hpr
    change r.val < p.val at hpr
    simp only [VBt, uB, uBTilde, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> simp_all [bracketB, paperIndex]
    all_goals split_ifs <;> first | omega | ring_nf
  rw [det_of_isUpperTriangular ht]
  clear ht
  have hd (r : Fin n) : VBt (n := n) (k := 0) t r r = 1 + t^(r.val+1) := by
    simp only [VBt, uB, uBTilde, bracketB, paperIndex, Nat.cast_zero, zero_add]
    split_ifs <;> simp_all [bracketB, paperIndex]
    all_goals split_ifs <;> first | omega | ring_nf
  simp only [hd, ExternalHL.pochhammer]
  apply Finset.prod_congr rfl
  intro r _
  ring

end
end AffineDualJT
