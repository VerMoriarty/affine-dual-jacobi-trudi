import AffineDualJT.BracketEvaluation

/-! # Evaluating the finite columns of Table 1 -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem PhiPlus_VBplus_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (PhiPlus (k := k) x * VBplus (n := n) (k := k) t) a r =
      if r.val=0 then Cfun (k:ℤ) (x a : F) else
        Cfun ((k:ℤ)+(r.val:ℤ)) (x a : F) +
          t^r.val*Cfun ((k:ℤ)-(r.val:ℤ)) (x a : F) := by
  have hr := r.isLt
  have hsum (v : Fin (n+k) → F) (c : F) :
      (∑ p : Fin (n+k), PhiPlus x a p*(c*v p)) =
        c*(∑ p : Fin (n+k), PhiPlus x a p*v p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [Matrix.mul_apply]
  by_cases hr0 : r.val=0
  · simp only [VBplus,uPlus,hr0,ite_true]
    rw [PhiPlus_bracket (k := k) x a ((k:ℤ)+1) (by omega) (by omega)]
    congr 1
    ring
  · simp only [VBplus,uPlus,hr0,ite_false,mul_add,Finset.sum_add_distrib]
    rw [hsum]
    rw [PhiPlus_bracket (k := k) x a ((k:ℤ)+paperIndex r) (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),
      PhiPlus_bracket (k := k) x a ((k:ℤ)+2-paperIndex r) (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
    simp only [paperIndex]
    congr 2 <;> ring_nf

theorem PhiPlus_VBplus_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (PhiPlus (k := k) x * VBplus (n := n) (k := k) t) a r =
      if r.val=0 then Cfun (k:ℤ) (x a : F) else
        Cfun ((k:ℤ)+(r.val:ℤ)) (x a : F) +
          t^r.val*Cfun ((k:ℤ)-(r.val:ℤ)) (x a : F) := PhiPlus_VBplus_apply_all_width (k := k) x t a r

theorem weighted_fColumn (t z : F) (hz : z≠0) (r : Fin n) :
    z^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r z =
      if r.val=0 then z^(-(k:ℤ)) else
        z^(-(k:ℤ)-(r.val:ℤ)) + t^r.val*z^((r.val:ℤ)-(k:ℤ)) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [fColumn,hr0,ite_true,← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    omega
  · simp only [fColumn,hr0,ite_false,mul_add,← zpow_natCast z]
    rw [mul_left_comm (z^(-((n:ℤ)+(k:ℤ)-1))) (t^r.val),
      ← zpow_add₀ hz, ← zpow_add₀ hz]
    rw [show -((n:ℤ)+(k:ℤ)-1)+((n-(r.val+1):ℕ):ℤ) = -(k:ℤ)-(r.val:ℤ) by omega,
      show -((n:ℤ)+(k:ℤ)-1)+((n+r.val-1:ℕ):ℤ) = (r.val:ℤ)-(k:ℤ) by omega]

theorem weighted_fColumn_plus_fold_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (x a : F)^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r (x a : F) +
      ((x a : F)⁻¹)^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r (x a : F)⁻¹ =
        (PhiPlus (k := k) x * VBplus (n := n) (k := k) t) a r := by
  rw [weighted_fColumn t _ (Units.ne_zero _),
    weighted_fColumn t _ (inv_ne_zero (Units.ne_zero _)),PhiPlus_VBplus_apply_all_width (k := k) x t]
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true,_root_.inv_zpow,← _root_.zpow_neg,neg_neg,Cfun]
    ring
  · simp only [hr0,ite_false,_root_.inv_zpow,← _root_.zpow_neg,neg_neg,Cfun]
    rw [show -(-(k:ℤ)-(r.val:ℤ))=(k:ℤ)+(r.val:ℤ) by ring,
      show -((r.val:ℤ)-(k:ℤ))=(k:ℤ)-(r.val:ℤ) by ring,
      show -((k:ℤ)+(r.val:ℤ))= -(k:ℤ)-(r.val:ℤ) by ring,
      show -((k:ℤ)-(r.val:ℤ))=(r.val:ℤ)-(k:ℤ) by ring]
    ring

/-- Linearity of evaluation against two finite bracket columns. -/

theorem weighted_fColumn_plus_fold (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (x a : F)^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r (x a : F) +
      ((x a : F)⁻¹)^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r (x a : F)⁻¹ =
        (PhiPlus (k := k) x * VBplus (n := n) (k := k) t) a r := weighted_fColumn_plus_fold_all_width (k := k) x t a r

theorem finite_column_pairing (A v w : Fin (n+k) → F) (c : F) :
    (∑ p : Fin (n+k), A p*(v p+c*w p)) =
      (∑ p : Fin (n+k), A p*v p)+c*(∑ p : Fin (n+k), A p*w p) := by
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem PhiC_uC_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiC x a p*uC (n := n) (k := k) t r p) =
      if r.val=0 then phi ((k:ℤ)+1) (x a : F) else
        phi ((k:ℤ)+paperIndex r+1-1) (x a : F)+
          t^r.val*phi ((k:ℤ)+1+1-paperIndex r) (x a : F) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [uC,hr0,ite_true]
    rw [PhiC_bracket (k := k) x a _ (by omega) (by omega)]
  · simp only [uC,hr0,ite_false]
    rw [finite_column_pairing]
    rw [PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),
      PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
    congr 2
    ring

theorem PhiC_uC_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiC x a p*uC (n := n) (k := k) t r p) =
      if r.val=0 then phi ((k:ℤ)+1) (x a : F) else
        phi ((k:ℤ)+paperIndex r+1-1) (x a : F)+
          t^r.val*phi ((k:ℤ)+1+1-paperIndex r) (x a : F) := PhiC_uC_apply_all_width (k := k) x t a r

theorem PhiC_uCTilde_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiC x a p*uCTilde (n := n) (k := k) t r p) =
      if r.val=0 then phi ((k:ℤ)+0) (x a : F) else
        phi ((k:ℤ)+paperIndex r+0-1) (x a : F)+
          t^r.val*phi ((k:ℤ)+0+1-paperIndex r) (x a : F) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [uCTilde,hr0,ite_true]
    rw [PhiC_bracket (k := k) x a _ (by omega) (by omega)]
    all_goals simp only [add_zero]
  · simp only [uCTilde,hr0,ite_false]
    rw [finite_column_pairing]
    rw [PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),
      PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
    congr 2

theorem PhiC_uCTilde_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiC x a p*uCTilde (n := n) (k := k) t r p) =
      if r.val=0 then phi ((k:ℤ)+0) (x a : F) else
        phi ((k:ℤ)+paperIndex r+0-1) (x a : F)+
          t^r.val*phi ((k:ℤ)+0+1-paperIndex r) (x a : F) := PhiC_uCTilde_apply_all_width (k := k) x t a r

theorem PhiB_uB_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiB x a p*uB (n := n) (k := k) t r p) =
      if r.val=0 then psi ((k:ℤ)+1) (x a : F) else
        psi ((k:ℤ)+paperIndex r+1-1) (x a : F)+
          t^r.val*psi ((k:ℤ)+1+1-paperIndex r) (x a : F) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [uB,hr0,ite_true]
    rw [PhiB_bracket (k := k) x a _ (by omega) (by omega)]
  · simp only [uB,hr0,ite_false]
    rw [finite_column_pairing]
    rw [PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),
      PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
    congr 2
    ring

theorem PhiB_uB_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiB x a p*uB (n := n) (k := k) t r p) =
      if r.val=0 then psi ((k:ℤ)+1) (x a : F) else
        psi ((k:ℤ)+paperIndex r+1-1) (x a : F)+
          t^r.val*psi ((k:ℤ)+1+1-paperIndex r) (x a : F) := PhiB_uB_apply_all_width (k := k) x t a r

theorem PhiB_uBTilde_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiB x a p*uBTilde (n := n) (k := k) t r p) =
      if r.val=0 then psi ((k:ℤ)+0) (x a : F) else
        psi ((k:ℤ)+paperIndex r+0-1) (x a : F)+
          t^r.val*psi ((k:ℤ)+0+1-paperIndex r) (x a : F) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [uBTilde,hr0,ite_true]
    rw [PhiB_bracket (k := k) x a _ (by omega) (by omega)]
    all_goals simp only [add_zero]
  · simp only [uBTilde,hr0,ite_false]
    rw [finite_column_pairing]
    rw [PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega),
      PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
        (by simp only [paperIndex]; omega)]
    congr 2

theorem PhiB_uBTilde_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (∑ p : Fin (n+k), PhiB x a p*uBTilde (n := n) (k := k) t r p) =
      if r.val=0 then psi ((k:ℤ)+0) (x a : F) else
        psi ((k:ℤ)+paperIndex r+0-1) (x a : F)+
          t^r.val*psi ((k:ℤ)+0+1-paperIndex r) (x a : F) := PhiB_uBTilde_apply_all_width (k := k) x t a r

theorem PhiC_VCt_apply_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (PhiC (k := k) x*VCt (n := n) (k := k) t) a r =
      phi ((k:ℤ)+paperIndex r) (x a : F)-
        t^(r.val+1)*phi ((k:ℤ)-paperIndex r) (x a : F) := by
  have hr := r.isLt
  rw [Matrix.mul_apply]
  simp only [VCt,sub_eq_add_neg,← neg_mul]
  rw [finite_column_pairing]
  rw [PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    PhiC_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]

theorem PhiC_VCt_apply (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (PhiC (k := k) x*VCt (n := n) (k := k) t) a r =
      phi ((k:ℤ)+paperIndex r) (x a : F)-
        t^(r.val+1)*phi ((k:ℤ)-paperIndex r) (x a : F) := PhiC_VCt_apply_all_width (k := k) x t a r

theorem PhiB_VBminus_apply_all_width (x : Fin n → Fˣ) (τ : F)
    (a : Fin n) (r : Fin n) :
    (PhiB (k := k) x*VBminus (n := n) (k := k) τ) a r =
      psi ((k:ℤ)+paperIndex r) (x a : F)+
        τ^(2*r.val+1)*psi ((k:ℤ)+1-paperIndex r) (x a : F) := by
  have hr := r.isLt
  rw [Matrix.mul_apply]
  simp only [VBminus]
  rw [finite_column_pairing]
  rw [PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega),
    PhiB_bracket (k := k) x a _ (by simp only [paperIndex]; omega)
      (by simp only [paperIndex]; omega)]

theorem PhiB_VBminus_apply (x : Fin n → Fˣ) (τ : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (PhiB (k := k) x*VBminus (n := n) (k := k) τ) a r =
      psi ((k:ℤ)+paperIndex r) (x a : F)+
        τ^(2*r.val+1)*psi ((k:ℤ)+1-paperIndex r) (x a : F) := PhiB_VBminus_apply_all_width (k := k) x τ a r

end
end AffineDualJT
