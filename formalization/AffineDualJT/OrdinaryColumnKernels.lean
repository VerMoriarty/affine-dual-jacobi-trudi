import AffineDualJT.OrdinarySequences
import AffineDualJT.BracketEvaluation
import AffineDualJT.FiniteColumnEvaluation

/-! # The second kernel relation for ordinary affine columns, source.tex §4 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem cC0_zero (t : F) (j : Fin k) : cC0Seq t j 0=0 := by
  simp [cC0Seq]

theorem cC0_fixed [CharZero F] (t : F) (ht : t≠0) (j : Fin k) :
    cC0Seq t j ((k:ℤ)+1)=0 := by
  have h := cC0_affine t ht j ((k:ℤ)+1)
  rw [show (k:ℤ)+1-(k:ℤ)-1=0 by ring,
    show 2*(k:ℤ)+2-((k:ℤ)+1)=(k:ℤ)+1 by ring,zpow_zero,one_mul] at h
  have htwo : (2:F)*cC0Seq t j ((k:ℤ)+1)=0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The second kernel relation in the `C0` proof of Proposition 4.1. -/
theorem VC0_transpose_CC [CharZero F] (t : F) (ht : t≠0) (hk : 0<k) :
    (VC0 (n := n) (k := k) t).transpose*CC (n := n) (k := k) (bC0Seq t)=(0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : -((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketC m p*CC (n := n) (k := k) (bC0Seq t) p j)=cC0Seq t j m := by
    exact bracketC_sum (cC0Seq t j) (cC0_neg t j) (cC0_zero t j) m hlo hhi
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VC0,uC,transpose_apply,hr0,ite_true,Matrix.zero_apply]
    rw [heval _ (by omega) (by omega),cC0_fixed t ht]
  · simp only [VC0,uC,transpose_apply,hr0,ite_false,Matrix.zero_apply]
    rw [show (∑ p : Fin (n+k),
      (bracketC ((k:ℤ)+paperIndex r) p+
        t^r.val*bracketC ((k:ℤ)+2-paperIndex r) p)*CC (n := n) (k := k) (bC0Seq t) p j) =
      (∑ p : Fin (n+k), bracketC ((k:ℤ)+paperIndex r) p*CC (n := n) (k := k) (bC0Seq t) p j)+
        t^r.val*(∑ p : Fin (n+k), bracketC ((k:ℤ)+2-paperIndex r) p*CC (n := n) (k := k) (bC0Seq t) p j) by
          simpa only [mul_comm] using finite_column_pairing
            (fun p => CC (n := n) (k := k) (bC0Seq t) p j)
            (bracketC ((k:ℤ)+paperIndex r)) (bracketC ((k:ℤ)+2-paperIndex r)) (t^r.val)]
    rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
    have h := cC0_affine t ht j ((k:ℤ)+paperIndex r)
    rw [show (k:ℤ)+paperIndex r-(k:ℤ)-1=(r.val:ℤ) by simp only [paperIndex]; ring,
      show 2*(k:ℤ)+2-((k:ℤ)+paperIndex r)=(k:ℤ)+2-paperIndex r by ring,
      zpow_natCast] at h
    exact h

/-- Only `q=0` contributes within the principal interval in the `C0` sequence. -/
theorem bC0_small (t : F) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)+2) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)+2) :
    bC0Seq t j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_small (2*(k:ℤ)+2) (paperIndex j) m (by omega)
    (fun q => t^(((k:ℤ)+1)*q^2+paperIndex j*q)) hlo hhi
  change bC0Seq t j m=(if m=paperIndex j then
    t^(((k:ℤ)+1)*(0:ℤ)^2+paperIndex j*0) else 0) at h
  rw [show ((k:ℤ)+1)*(0:ℤ)^2+paperIndex j*0=0 by ring,zpow_zero] at h
  exact h

/-- The undoubled complementary head block in the `C0` case. -/
theorem CC_C0_head (t : F) :
    firstRowsZ (CC (n := n) (k := k) (bC0Seq t))=1 := by
  ext p j
  change cC0Seq t j (paperIndex p)=(if p=j then 1 else 0)
  have hp := p.isLt
  have hj := j.isLt
  have hneg : -paperIndex p≠paperIndex j := by
    have hpp := paperIndex_pos p
    have hjp := paperIndex_pos j
    omega
  unfold cC0Seq
  rw [bC0_small t j (paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    bC0_small t j (-paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
  simp only [paperIndex_injective.eq_iff,hneg,ite_false,sub_zero]

end
end AffineDualJT
