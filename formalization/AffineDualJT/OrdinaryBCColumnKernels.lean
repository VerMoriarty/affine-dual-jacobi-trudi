import AffineDualJT.OrdinaryColumnKernels

/-! # The second kernel and the undoubled head in Proposition 4.1, BC -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem cBC_zero (τ : F) (j : Fin k) : cBCSeq τ j 0=0 := by
  simp [cBCSeq]

/-- The four column terms split into the two affine reflections in §4.1. -/
theorem VBC_transpose_CC (τ : F) (hτ : τ≠0) (hk : 0<k) :
    (VBC (n := n) (k := k) τ).transpose*CC (n := n) (k := k) (bBCSeq τ)=
      (0 : Matrix (Fin n) (Fin k) F) := by
  ext r j
  have hr := r.isLt
  have heval (m : ℤ) (hlo : -((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), bracketC m p*CC (n := n) (k := k) (bBCSeq τ) p j)=cBCSeq τ j m := by
    exact bracketC_sum (cBCSeq τ j) (cBC_neg τ j) (cBC_zero τ j) m hlo hhi
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VBC,uC,uCTilde,transpose_apply,hr0,ite_true,Matrix.zero_apply,
      add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [heval _ (by omega) (by omega),heval _ (by omega) (by omega)]
    have h := cBC_affine τ hτ j ((k:ℤ)+1)
    rw [show 2*((k:ℤ)+1)-(2*(k:ℤ)+1)=1 by ring,
      show 2*(k:ℤ)+1-((k:ℤ)+1)=(k:ℤ) by ring,zpow_one] at h
    exact h
  · simp only [VBC,uC,uCTilde,transpose_apply,hr0,ite_false,Matrix.zero_apply,
      add_mul,mul_add,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega),
      heval _ (by simp only [paperIndex]; omega) (by simp only [paperIndex]; omega)]
    have h₁ := cBC_affine τ hτ j ((k:ℤ)+paperIndex r)
    have h₂ := cBC_affine τ hτ j ((k:ℤ)+paperIndex r-1)
    rw [show 2*((k:ℤ)+paperIndex r)-(2*(k:ℤ)+1)=((2*r.val+1:ℕ):ℤ) by
        simp only [paperIndex]; push_cast; ring,
      show 2*(k:ℤ)+1-((k:ℤ)+paperIndex r)=(k:ℤ)+1-paperIndex r by ring,
      zpow_natCast,pow_add,pow_one,pow_mul] at h₁
    rw [show 2*((k:ℤ)+paperIndex r-1)-(2*(k:ℤ)+1)=2*(r.val:ℤ)-1 by
        simp only [paperIndex]; ring,
      show 2*(k:ℤ)+1-((k:ℤ)+paperIndex r-1)=(k:ℤ)+2-paperIndex r by ring] at h₂
    have hp : τ*τ^(2*(r.val:ℤ)-1)=(τ^2)^r.val := by
      calc
        _ = τ^(1+(2*(r.val:ℤ)-1)) := by rw [zpow_add₀ hτ,zpow_one]
        _ = (τ^2)^r.val := by
          rw [show 1+(2*(r.val:ℤ)-1)=((2*r.val:ℕ):ℤ) by push_cast; ring,
            zpow_natCast,pow_mul]
    have h₂' := congrArg (fun z : F => τ*z) h₂
    simp only [mul_add,← mul_assoc,mul_zero,hp] at h₂'
    linear_combination h₁+h₂'

theorem bBC_small (τ : F) (j : Fin k) (m : ℤ)
    (hlo : -(2*(k:ℤ)+1) < m-paperIndex j)
    (hhi : m-paperIndex j < 2*(k:ℤ)+1) :
    bBCSeq τ j m=if m=paperIndex j then 1 else 0 := by
  have h := residueSum_small (2*(k:ℤ)+1) (paperIndex j) m (by omega)
    (fun q => τ^((2*(k:ℤ)+1)*q^2+2*paperIndex j*q)) hlo hhi
  change bBCSeq τ j m=(if m=paperIndex j then
    τ^((2*(k:ℤ)+1)*(0:ℤ)^2+2*paperIndex j*0) else 0) at h
  rw [show (2*(k:ℤ)+1)*(0:ℤ)^2+2*paperIndex j*0=0 by ring,zpow_zero] at h
  exact h

theorem CC_BC_head (τ : F) :
    firstRowsZ (CC (n := n) (k := k) (bBCSeq τ))=1 := by
  ext p j
  change cBCSeq τ j (paperIndex p)=(if p=j then 1 else 0)
  have hp := p.isLt
  have hj := j.isLt
  have hneg : -paperIndex p≠paperIndex j := by
    have := paperIndex_pos p
    have := paperIndex_pos j
    omega
  unfold cBCSeq
  rw [bBC_small τ j (paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    bBC_small τ j (-paperIndex p) (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]
  simp only [paperIndex_injective.eq_iff,hneg,ite_false,sub_zero]

end
end AffineDualJT
