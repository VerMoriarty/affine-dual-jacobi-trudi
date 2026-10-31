import AffineDualJT.ExceptionalBplusKernels

/-! # Adjacent-residue kernels and the doubled head for Proposition 5.5 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem cBt_first (t : F) (j : Fin k) (m : ℤ) : cBt t j (1-m)=-cBt t j m := by
  simp only [cBt,← Int.cast_negOnePow F,Int.negOnePow_sub]
  norm_num
  ring

theorem CB_Bt_apply (t : F) (p : Fin (n+k)) (j : Fin k) :
    CB (n := n) (aBt t) p j=cBt t j (paperIndex p) := by
  unfold CB cBt
  rw [show paperIndex p=((p.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]

theorem VBt_transpose_CB [CharZero F] (t : F) (ht : t≠0) (hk : 0<k) :
    (VBt (n := n) (k := k) t).transpose*CB (n := n) (k := k) (aBt t)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : 1-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketB m p*CB (n := n) (aBt t) p j)=cBt t j m := by
    simp only [CB_Bt_apply]
    exact bracketB_sum (cBt t j) (cBt_first t j) m hlo hhi
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VBt,uB,uBTilde,transpose_apply,hr0,ite_true,Matrix.zero_apply,
      sub_mul,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [heval _ (by omega) (by omega),heval _ (by omega) (by omega)]
    have h := lemma_5_4_fixed t ht j
    simpa only [gammaBt,add_sub_cancel_right] using h
  · simp only [VBt,uB,uBTilde,transpose_apply,hr0,ite_false,Matrix.zero_apply,
      sub_mul,add_mul,mul_add,mul_assoc,Finset.sum_sub_distrib,
      Finset.sum_add_distrib,← Finset.mul_sum]
    rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
    have h := lemma_5_4_eq_5_5 t ht j ((k:ℤ)+paperIndex r)
    rw [show (k:ℤ)+paperIndex r-(k:ℤ)-1=(r.val:ℤ) by simp only [paperIndex]; ring,
      show 2*(k:ℤ)+2-((k:ℤ)+paperIndex r)=(k:ℤ)+2-paperIndex r by ring,
      zpow_natCast] at h
    simp only [gammaBt,show (k:ℤ)+2-paperIndex r-1=(k:ℤ)+1-paperIndex r by ring] at h
    linear_combination h

/-- Explicit upper bidiagonal head, with the additional `(1,1)` overlap. -/
theorem CB_Bt_head_entry (t : F) (hk : 0<k) (p j : Fin k) :
    firstRowsZ (CB (n := n) (k := k) (aBt t)) p j=
      (-1:F)^(p.val+1)*((if p=j then 1 else 0)+
        (if paperIndex p+1=paperIndex j then 1 else 0)+
        (if p.val=0 ∧ j.val=0 then 1 else 0)) := by
  have hp := p.isLt
  have hj := j.isLt
  change (-1:F)^(p.val+1)*
    ((bBplus t j (paperIndex p)+bBplus t j (paperIndex p+1))+
      (bBplus t j (1-paperIndex p)+bBplus t j (1-paperIndex p+1)))=_
  rw [bBplus_small t hk j (paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    bBplus_small t hk j (paperIndex p+1) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    bBplus_small t hk j (1-paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    bBplus_small t hk j (1-paperIndex p+1) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
  have hne : 1-paperIndex p≠paperIndex j := by simp only [paperIndex]; omega
  have he : 1-paperIndex p+1=paperIndex j ↔ p.val=0 ∧ j.val=0 := by
    simp only [paperIndex]; omega
  simp only [paperIndex_injective.eq_iff,hne,ite_false,he,zero_add,add_assoc]

theorem CB_Bt_head (t : F) (hk : 0<k) :
    (firstRowsZ (CB (n := n) (k := k) (aBt t))).det=2*omegaSign F k := by
  classical
  rw [det_of_isUpperTriangular]
  · have he : ∀ p : Fin k, firstRowsZ (CB (n := n) (k := k) (aBt t)) p p=
        (-1:F)^(p.val+1)*(if p.val=0 then 2 else 1) := by
      intro p
      rw [CB_Bt_head_entry t hk]
      simp only [ite_true,show paperIndex p+1≠paperIndex p by omega,ite_false,and_self]
      by_cases hp : p.val=0 <;> simp [hp]
      ring
    simp_rw [he]
    rw [Finset.prod_mul_distrib,prod_first_sign]
    have hp : (∏ p : Fin k, if p.val=0 then (2:F) else 1)=2 := by
      have he : ∀ p : Fin k, p.val=0 ↔ p=⟨0,hk⟩ := by
        intro p
        exact (Fin.ext_iff (a := p) (b := ⟨0,hk⟩)).symm
      simp_rw [he]
      simp
    rw [hp,mul_comm]
  · intro p j hpj
    rw [CB_Bt_head_entry t hk]
    have hpj' : j.val < p.val := hpj
    have hne : p≠j := by intro h; subst j; omega
    have hnext : paperIndex p+1≠paperIndex j := by simp only [paperIndex]; omega
    have hcenter : ¬(p.val=0 ∧ j.val=0) := by omega
    simp only [hne,hnext,hcenter,ite_false,zero_add,mul_zero]

end
end AffineDualJT
