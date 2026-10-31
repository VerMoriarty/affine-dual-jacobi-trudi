import AffineDualJT.OrdinaryColumnKernels
import AffineDualJT.ClassicalTransfer

/-! # The second kernels and head minors for Proposition 4.2 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem CB_B0_apply (t : F) (p : Fin (n+k)) (j : Fin k) :
    CB (n := n) (k := k) (bB0Seq t) p j=gammaB0 t j (paperIndex p) := by
  unfold CB gammaB0
  rw [show paperIndex p=((p.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]

theorem CB_Bminus_apply (τ : F) (p : Fin (n+k)) (j : Fin k) :
    CB (n := n) (k := k) (bBminusSeq τ) p j=gammaBminus τ j (paperIndex p) := by
  unfold CB gammaBminus
  rw [show paperIndex p=((p.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]

theorem gammaB0_fixed [CharZero F] (t : F) (ht : t≠0) (j : Fin k) :
    gammaB0 t j ((k:ℤ)+1)=0 := by
  have h := gammaB0_second t ht j ((k:ℤ)+1)
  rw [show (k:ℤ)+1-(k:ℤ)-1=0 by ring,
    show 2*(k:ℤ)+2-((k:ℤ)+1)=(k:ℤ)+1 by ring,zpow_zero] at h
  have htwo : (2:F)*gammaB0 t j ((k:ℤ)+1)=0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Equation (4.2) evaluated against the finite `B0` columns. -/
theorem VB0_transpose_CB [CharZero F] (t : F) (ht : t≠0) (hk : 0<k) :
    (VB0 (n := n) (k := k) t).transpose*CB (n := n) (k := k) (bB0Seq t)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : 1-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketB m p*CB (n := n) (k := k) (bB0Seq t) p j)=gammaB0 t j m := by
    simp only [CB_B0_apply]
    exact bracketB_sum (gammaB0 t j) (gammaB0_first t j) m hlo hhi
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VB0,uB,transpose_apply,hr0,ite_true,Matrix.zero_apply]
    rw [heval _ (by omega) (by omega),gammaB0_fixed t ht]
  · simp only [VB0,uB,transpose_apply,hr0,ite_false,Matrix.zero_apply]
    rw [show (∑ p : Fin (n+k),
      (bracketB ((k:ℤ)+paperIndex r) p+
        t^r.val*bracketB ((k:ℤ)+2-paperIndex r) p)*CB (n := n) (k := k) (bB0Seq t) p j) =
      (∑ p : Fin (n+k), bracketB ((k:ℤ)+paperIndex r) p*CB (n := n) (k := k) (bB0Seq t) p j)+
        t^r.val*(∑ p : Fin (n+k), bracketB ((k:ℤ)+2-paperIndex r) p*CB (n := n) (k := k) (bB0Seq t) p j) by
          simpa only [mul_comm] using finite_column_pairing
            (fun p => CB (n := n) (k := k) (bB0Seq t) p j)
            (bracketB ((k:ℤ)+paperIndex r)) (bracketB ((k:ℤ)+2-paperIndex r)) (t^r.val)]
    rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
    have h := gammaB0_second t ht j ((k:ℤ)+paperIndex r)
    rw [show (k:ℤ)+paperIndex r-(k:ℤ)-1=(r.val:ℤ) by simp only [paperIndex]; ring,
      show 2*(k:ℤ)+2-((k:ℤ)+paperIndex r)=(k:ℤ)+2-paperIndex r by ring,
      zpow_natCast] at h
    linear_combination h

/-- Equation (4.2) evaluated against the finite `B-` columns. -/
theorem VBminus_transpose_CB (τ : F) (hτ : τ≠0) (hk : 0<k) :
    (VBminus (n := n) (k := k) τ).transpose*CB (n := n) (k := k) (bBminusSeq τ)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : 1-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketB m p*CB (n := n) (k := k) (bBminusSeq τ) p j)=gammaBminus τ j m := by
    simp only [CB_Bminus_apply]
    exact bracketB_sum (gammaBminus τ j) (gammaBminus_first τ j) m hlo hhi
  rw [Matrix.mul_apply]
  simp only [VBminus,transpose_apply,Matrix.zero_apply]
  rw [show (∑ p : Fin (n+k),
    (bracketB ((k:ℤ)+paperIndex r) p+
      τ^(2*r.val+1)*bracketB ((k:ℤ)+1-paperIndex r) p)*CB (n := n) (k := k) (bBminusSeq τ) p j) =
    (∑ p : Fin (n+k), bracketB ((k:ℤ)+paperIndex r) p*CB (n := n) (k := k) (bBminusSeq τ) p j)+
      τ^(2*r.val+1)*(∑ p : Fin (n+k), bracketB ((k:ℤ)+1-paperIndex r) p*CB (n := n) (k := k) (bBminusSeq τ) p j) by
        simpa only [mul_comm] using finite_column_pairing
          (fun p => CB (n := n) (k := k) (bBminusSeq τ) p j)
          (bracketB ((k:ℤ)+paperIndex r)) (bracketB ((k:ℤ)+1-paperIndex r)) (τ^(2*r.val+1))]
  rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
    heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
  have h := gammaBminus_second τ hτ j ((k:ℤ)+paperIndex r)
  rw [show 2*((k:ℤ)+paperIndex r)-2*(k:ℤ)-1=((2*r.val+1:ℕ):ℤ) by simp only [paperIndex]; push_cast; ring,
    show 2*(k:ℤ)+1-((k:ℤ)+paperIndex r)=(k:ℤ)+1-paperIndex r by ring,zpow_natCast] at h
  linear_combination h

theorem bB0_small (t : F) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)+1) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)+1) :
    bB0Seq t j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_minus_small (2*(k:ℤ)+1) (paperIndex j) m (by omega)
    (fun y => (-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2)) hlo hhi
  change bB0Seq t j m=(if m=paperIndex j then
    (-1:F)^(0:ℤ)*t^(((2*(k:ℤ)+1)*(0:ℤ)^2-(2*paperIndex j-1)*0)/2) else 0) at h
  norm_num only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,Int.zero_ediv,zpow_zero,one_mul] at h
  exact h

theorem bBminus_small (τ : F) (hk : 0<k) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)) :
    bBminusSeq τ j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_minus_small (2*(k:ℤ)) (paperIndex j) m (by omega)
    (fun y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y)) hlo hhi
  change bBminusSeq τ j m=(if m=paperIndex j then
    τ^((2*(k:ℤ))*(0:ℤ)^2-(2*paperIndex j-1)*0) else 0) at h
  rw [show (2*(k:ℤ))*(0:ℤ)^2-(2*paperIndex j-1)*0=0 by ring,zpow_zero] at h
  exact h

/-- In both type B cases the principal head has the alternating column signs. -/
theorem CB_head_of_small (b : Fin k → ℤ → F)
    (hpos : ∀ p j : Fin k, b j (paperIndex p)=if p=j then 1 else 0)
    (href : ∀ p j : Fin k, b j (1-paperIndex p)=0) :
    (firstRowsZ (CB (n := n) b)).det=omegaSign F k := by
  classical
  have hm : firstRowsZ (CB (n := n) b)=
      Matrix.of fun p j : Fin k => (-1:F)^(p.val+1)*(1 : Matrix (Fin k) (Fin k) F) p j := by
    ext p j
    change (-1:F)^(p.val+1)*(b j (paperIndex p)+b j (1-paperIndex p))=_
    rw [hpos,href,add_zero]
    rfl
  rw [hm,det_mul_column,det_one,mul_one,prod_first_sign]

theorem CB_B0_head (t : F) :
    (firstRowsZ (CB (n := n) (k := k) (bB0Seq t))).det=omegaSign F k := by
  apply CB_head_of_small
  · intro p j
    have hp := p.isLt
    have hj := j.isLt
    rw [bB0_small t j (paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
    simp only [paperIndex_injective.eq_iff]
  · intro p j
    have hp := p.isLt
    have hj := j.isLt
    have hne : 1-paperIndex p≠paperIndex j := by
      have := paperIndex_pos p
      have := paperIndex_pos j
      omega
    rw [bB0_small t j (1-paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),ite_eq_right hne]

theorem CB_Bminus_head (τ : F) (hk : 0<k) :
    (firstRowsZ (CB (n := n) (k := k) (bBminusSeq τ))).det=omegaSign F k := by
  apply CB_head_of_small
  · intro p j
    have hp := p.isLt
    have hj := j.isLt
    rw [bBminus_small τ hk j (paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
    simp only [paperIndex_injective.eq_iff]
  · intro p j
    have hp := p.isLt
    have hj := j.isLt
    have hne : 1-paperIndex p≠paperIndex j := by
      have := paperIndex_pos p
      have := paperIndex_pos j
      omega
    rw [bBminus_small τ hk j (1-paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),ite_eq_right hne]

end
end AffineDualJT
