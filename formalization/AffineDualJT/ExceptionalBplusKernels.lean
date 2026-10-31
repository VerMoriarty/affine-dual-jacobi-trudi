import AffineDualJT.ExceptionalSequences
import AffineDualJT.PlusFoldEvaluation
import AffineDualJT.ClassicalTransfer
import AffineDualJT.FiniteColumnEvaluation

/-! # The normalized center kernel and head minor for Proposition 5.3 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- The first row is `-b_j(1)`, so its doubled bracket gives `Γ_j(1)`. -/
theorem CPlus_Bplus_center (t : F) (j : Fin k) (p : Fin (n+k)) (hp : p.val=0) :
    2*CPlus (n := n) (bBplus t) p j=Gamma t j 1 := by
  simp only [CPlus,hp,ite_true,Gamma,zpow_one,show (2:ℤ)-1=1 by ring]
  ring

theorem CPlus_Bplus_positive (t : F) (j : Fin k) (p : Fin (n+k)) (hp : p.val≠0) :
    CPlus (n := n) (bBplus t) p j=Gamma t j (paperIndex p) := by
  simp only [CPlus,hp,ite_false,Gamma]
  rw [show paperIndex p=((p.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]

/-- All brackets evaluate to `Γ`, including the nonvanishing center. -/
theorem bracketPlus_CPlus_Bplus (t : F) (j : Fin k) (m : ℤ)
    (hlo : 2-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
    (∑ p : Fin (n+k), bracketPlus m p*CPlus (n := n) (bBplus t) p j)=Gamma t j m := by
  exact bracketPlus_sum_normalized (Gamma t j) (lemma_5_2_center t j)
    (fun p => CPlus (n := n) (bBplus t) p j)
    (CPlus_Bplus_center t j) (CPlus_Bplus_positive t j) m hlo hhi

theorem VBplus_transpose_CPlus [CharZero F] (t : F) (ht : t≠0) (hk : 0<k) :
    (VBplus (n := n) (k := k) t).transpose*CPlus (n := n) (k := k) (bBplus t)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval := bracketPlus_CPlus_Bplus (n := n) t j
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VBplus,uPlus,transpose_apply,hr0,ite_true,Matrix.zero_apply]
    rw [heval _ (by omega) (by omega),lemma_5_2_fixed t ht]
  · simp only [VBplus,uPlus,transpose_apply,hr0,ite_false,Matrix.zero_apply]
    rw [show (∑ p : Fin (n+k),
      (bracketPlus ((k:ℤ)+paperIndex r) p+
        t^r.val*bracketPlus ((k:ℤ)+2-paperIndex r) p)*CPlus (n := n) (bBplus t) p j) =
      (∑ p : Fin (n+k), bracketPlus ((k:ℤ)+paperIndex r) p*CPlus (n := n) (bBplus t) p j)+
        t^r.val*(∑ p : Fin (n+k), bracketPlus ((k:ℤ)+2-paperIndex r) p*CPlus (n := n) (bBplus t) p j) by
          simpa only [mul_comm] using finite_column_pairing
            (fun p => CPlus (n := n) (bBplus t) p j)
            (bracketPlus ((k:ℤ)+paperIndex r)) (bracketPlus ((k:ℤ)+2-paperIndex r)) (t^r.val)]
    rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
    have h := lemma_5_2_affine t ht j ((k:ℤ)+paperIndex r)
    rw [show (k:ℤ)+paperIndex r-(k:ℤ)-1=(r.val:ℤ) by simp only [paperIndex]; ring,
      show 2*(k:ℤ)+2-((k:ℤ)+paperIndex r)=(k:ℤ)+2-paperIndex r by ring,
      zpow_natCast] at h
    linear_combination h

theorem bBplus_small (t : F) (hk : 0<k) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)) :
    bBplus t j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_minus_small (2*(k:ℤ)) (paperIndex j) m (by omega)
    (fun y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y)) hlo hhi
  change bBplus t j m=(if m=paperIndex j then
    (-1:F)^(0:ℤ)*t^((k:ℤ)*(0:ℤ)^2-(paperIndex j-1)*0) else 0) at h
  rw [show (k:ℤ)*(0:ℤ)^2-(paperIndex j-1)*0=0 by ring,zpow_zero,zpow_zero,one_mul] at h
  exact h

/-- The center is normalized; the complementary head has determinant `ω`. -/
theorem CPlus_Bplus_head (t : F) (hk : 0<k) :
    (firstRowsZ (CPlus (n := n) (k := k) (bBplus t))).det=omegaSign F k := by
  classical
  have hm : firstRowsZ (CPlus (n := n) (k := k) (bBplus t))=
      Matrix.of fun p j : Fin k => (-1:F)^(p.val+1)*(1 : Matrix (Fin k) (Fin k) F) p j := by
    ext p j
    have hp := p.isLt
    have hj := j.isLt
    have hpos : bBplus t j (paperIndex p)=if p=j then 1 else 0 := by
      rw [bBplus_small t hk j (paperIndex p) (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
      simp only [paperIndex_injective.eq_iff]
    change (if p.val=0 then -bBplus t j 1 else
      (-1:F)^(p.val+1)*(bBplus t j (paperIndex p)+bBplus t j (2-paperIndex p)))=_
    by_cases hp0 : p.val=0
    · rw [ite_eq_left hp0]
      rw [show paperIndex p=1 by simp [paperIndex,hp0]] at hpos
      rw [hpos]
      simp only [Matrix.of_apply,Matrix.one_apply,hp0,zero_add,pow_one,neg_one_mul]
    · rw [ite_eq_right hp0]
      have hne : 2-paperIndex p≠paperIndex j := by simp only [paperIndex]; omega
      rw [hpos,bBplus_small t hk j (2-paperIndex p) (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),ite_eq_right hne,add_zero]
      rfl
  rw [hm,det_mul_column,det_one,mul_one,prod_first_sign]

end
end AffineDualJT
