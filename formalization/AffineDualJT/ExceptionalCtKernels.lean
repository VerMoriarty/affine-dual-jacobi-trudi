import AffineDualJT.ExceptionalSequences
import AffineDualJT.OrdinaryColumnKernels
import AffineDualJT.ClassicalColumns

/-! # The fixed-residue kernel and doubled head in Proposition 5.1 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem cCt_neg (t : F) (j : Fin k) (m : ℤ) : cCt t j (-m)=-cCt t j m := by
  simp [cCt]

theorem cCt_zero (t : F) (j : Fin k) : cCt t j 0=0 := by simp [cCt]

theorem VCt_transpose_CC (t : F) (ht : t≠0) (hk : 0<k) :
    (VCt (n := n) (k := k) t).transpose*CC (n := n) (k := k) (bCt t)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : -((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketC m p*CC (n := n) (bCt t) p j)=cCt t j m := by
    exact bracketC_sum (cCt t j) (cCt_neg t j) (cCt_zero t j) m hlo hhi
  rw [Matrix.mul_apply]
  simp only [VCt,transpose_apply,Matrix.zero_apply,sub_mul,mul_assoc,
    Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
    heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
  have h := cCt_reflection t ht j ((k:ℤ)+paperIndex r)
  rw [show (k:ℤ)+paperIndex r-(k:ℤ)=((r.val+1:ℕ):ℤ) by simp [paperIndex],
    show 2*(k:ℤ)-((k:ℤ)+paperIndex r)=(k:ℤ)-paperIndex r by ring,zpow_natCast] at h
  exact sub_eq_zero.mpr h

theorem bCt_small (t : F) (hk : 0<k) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)) :
    bCt t j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_small (2*(k:ℤ)) (paperIndex j) m (by omega)
    (fun q => (-1:F)^q*t^((k:ℤ)*q^2+paperIndex j*q)) hlo hhi
  change bCt t j m=(if m=paperIndex j then
    (-1:F)^(0:ℤ)*t^((k:ℤ)*(0:ℤ)^2+paperIndex j*0) else 0) at h
  rw [show (k:ℤ)*(0:ℤ)^2+paperIndex j*0=0 by ring,zpow_zero,zpow_zero,one_mul] at h
  exact h

theorem cCt_head_entry (t : F) (hk : 0<k) (p j : Fin k) :
    cCt t j (paperIndex p)=
      if p=j then (if j.val+1=k then 2 else 1) else 0 := by
  have hp := paperIndex_pos p
  have hj := paperIndex_pos j
  have hpk := paperIndex_le p
  have hjk := paperIndex_le j
  have hpos : bCt t j (paperIndex p)=if p=j then 1 else 0 := by
    rw [bCt_small t hk j (paperIndex p) (by omega) (by omega)]
    simp only [paperIndex_injective.eq_iff]
  by_cases he : paperIndex p+paperIndex j=2*(k:ℤ)
  · have hpK : paperIndex p=(k:ℤ) := by omega
    have hjK : paperIndex j=(k:ℤ) := by omega
    have hpj : p=j := paperIndex_injective (hpK.trans hjK.symm)
    have hjlast : j.val+1=k := by simp only [paperIndex] at hjK; omega
    have hb := residue_point_eq (2*(k:ℤ)) (paperIndex j) (by omega)
      (fun q => (-1:F)^q*t^((k:ℤ)*q^2+paperIndex j*q)) (-1)
    change bCt t j (paperIndex j+2*(k:ℤ)*(-1))=
      (-1:F)^(-1:ℤ)*t^((k:ℤ)*(-1:ℤ)^2+paperIndex j*(-1)) at hb
    rw [show paperIndex j+2*(k:ℤ)*(-1)=-paperIndex p by omega,
      show (k:ℤ)*(-1:ℤ)^2+paperIndex j*(-1)=0 by rw [hjK]; ring,
      zpow_zero,mul_one] at hb
    rw [show (-1:F)^(-1:ℤ)=-1 by norm_num] at hb
    rw [cCt,hpos,hb,ite_eq_left hpj,ite_eq_left hpj,ite_eq_left hjlast]
    norm_num
  · have hneg : -paperIndex p≠paperIndex j := by omega
    have hboundary : ¬(p=j ∧ j.val+1=k) := by
      rintro ⟨rfl,h⟩
      apply he
      simp only [paperIndex]
      omega
    rw [cCt,hpos,bCt_small t hk j (-paperIndex p) (by omega) (by omega),ite_eq_right hneg,sub_zero]
    by_cases hpj : p=j
    · have hjlast : j.val+1≠k := by intro h; exact hboundary ⟨hpj,h⟩
      simp only [hpj,hjlast,ite_true,ite_false]
    · simp only [hpj,ite_false]

theorem CC_Ct_head (t : F) (hk : 0<k) :
    (firstRowsZ (CC (n := n) (k := k) (bCt t))).det=2 := by
  classical
  have hm : firstRowsZ (CC (n := n) (k := k) (bCt t))=
      diagonal (fun j : Fin k => if j.val+1=k then (2:F) else 1) := by
    ext p j
    change cCt t j (paperIndex p)=_
    rw [cCt_head_entry t hk,diagonal_apply]
    by_cases hpj : p=j <;> simp [hpj]
  rw [hm,det_diagonal]
  have he : ∀ j : Fin k, j.val+1=k ↔ j=⟨k-1,by omega⟩ := by
    intro j
    rw [Fin.ext_iff]
    change j.val+1=k ↔ j.val=k-1
    omega
  simp_rw [he]
  simp

/-- At zero parameter the fixed residue remains inside the first `k` rows. -/
theorem bCt_zero_outside (hk : 0<k) (j : Fin k) (m : ℤ)
    (hm : (k:ℤ) < m ∨ m < -(k:ℤ)) : bCt (0:F) j m=0 := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  have hkz : (0:ℤ)<k := by omega
  unfold bCt
  have hzero (q : ℤ) : (if m=paperIndex j+2*(k:ℤ)*q then
      (-1:F)^q*(0:F)^((k:ℤ)*q^2+paperIndex j*q) else 0)=0 := by
    by_cases he : m=paperIndex j+2*(k:ℤ)*q
    · rw [ite_eq_left he]
      have hexp : (k:ℤ)*q^2+paperIndex j*q≠0 := by
        rw [show (k:ℤ)*q^2+paperIndex j*q=q*((k:ℤ)*q+paperIndex j) by ring]
        intro h
        rcases mul_eq_zero.mp h with hq | hq
        · subst q
          simp only [mul_zero,add_zero] at he
          omega
        · have hqneg : q < 0 := by nlinarith
          have hqlo : -1 ≤ q := by
            by_contra h
            have hq2 : q ≤ -2 := by omega
            nlinarith
          have hq1 : q=-1 := by omega
          rw [hq1] at he hq
          rcases hm with hm | hm <;> nlinarith
      rw [_root_.zero_zpow _ hexp,mul_zero]
    · rw [ite_eq_right he]
  simp only [hzero,finsum_zero]

/-- The second kernel also holds at zero, by the coordinate-column support. -/
theorem VCt_transpose_CC_all (t : F) (hk : 0<k) :
    (VCt (n := n) (k := k) t).transpose*CC (n := n) (k := k) (bCt t)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  by_cases ht : t=0
  · subst t
    rw [VCt_zero]
    ext r j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    change (if p=(⟨k+r.val,by omega⟩ : Fin (n+k)) then (1:F) else 0)*
      (bCt 0 j (paperIndex p)-bCt 0 j (-paperIndex p))=0
    by_cases he : p=(⟨k+r.val,by omega⟩ : Fin (n+k))
    · rw [ite_eq_left he]
      have hpk : (k:ℤ) < paperIndex p := by rw [he]; simp only [paperIndex]; omega
      rw [bCt_zero_outside hk j _ (Or.inl hpk),
        bCt_zero_outside hk j _ (Or.inr (by omega)),sub_self,mul_zero]
    · rw [ite_eq_right he,zero_mul]
  · exact VCt_transpose_CC t ht hk

end
end AffineDualJT
