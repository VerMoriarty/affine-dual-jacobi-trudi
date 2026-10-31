import AffineDualJT.FiniteDeterminantTransfer
import AffineDualJT.FiniteRowFunctions

/-! # Proposition 2.2, the `C0`, `Ct`, `BC`, `B0`, `B-`, and `Bt` cases -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem finite_c0_ratio_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaC x≠0) :
    RedC0 x t k=(PhiC (k := k) x*VC0 (n := n) (k := k) t).det/DeltaC x := by
  have h := finiteC_from_alternant_all_width (k := k) x t hDelta (fColumn t) (fun _ => 1)
    (VC0 t) (by intro y; simpa only [Finset.prod_const_one,one_mul] using
      lemma_2_1_eq_2_3_of t (fun a => (y a : F)))
    (by
      intro a r
      have hf := finiteBasicRow_C_column_all_width (k := k) x t a r
      simpa only [finiteBasicRow,show -((n:ℤ)-1)-((k:ℤ)+1)= -(n:ℤ)-(k:ℤ) by ring]
        using hf)
  simpa only [RedC0,one_div] using h

theorem finite_c0_ratio (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaC x≠0) :
    RedC0 x t k=(PhiC (k := k) x*VC0 (n := n) (k := k) t).det/DeltaC x := finite_c0_ratio_all_width (k := k) x t hDelta

theorem finite_b0_ratio_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaB x≠0) :
    RedB0 x t k=(PhiB (k := k) x*VB0 (n := n) (k := k) t).det/DeltaB x := by
  have h := finiteB_from_alternant_all_width (k := k) x t hDelta (fColumn t) (fun _ => 1)
    (VB0 t) (by intro y; simpa only [Finset.prod_const_one,one_mul] using
      lemma_2_1_eq_2_3_of t (fun a => (y a : F)))
    (by
      intro a r
      have hf := finiteBasicRow_B_column_all_width (k := k) x t a r
      simpa only [finiteBasicRow,show -((n:ℤ)-1)-(k:ℤ)= -(n:ℤ)+1-(k:ℤ) by ring,
        mul_assoc] using hf)
  simpa only [RedB0,one_div] using h

theorem finite_b0_ratio (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaB x≠0) :
    RedB0 x t k=(PhiB (k := k) x*VB0 (n := n) (k := k) t).det/DeltaB x := finite_b0_ratio_all_width (k := k) x t hDelta

theorem finite_ct_ratio_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaC x≠0) :
    RedCt x t k=(PhiC (k := k) x*VCt (n := n) (k := k) t).det/DeltaC x := by
  apply finiteC_from_alternant_all_width (k := k) x t hDelta (ctAlternantColumn t)
    (fun z => 1-t*z^2) (VCt t)
  · intro y
    exact lemma_2_1_eq_2_4_of t (fun a => (y a : F))
  · intro a r
    exact finiteCtRow_column_all_width (k := k) x t a r

theorem finite_ct_ratio (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaC x≠0) :
    RedCt x t k=(PhiC (k := k) x*VCt (n := n) (k := k) t).det/DeltaC x := finite_ct_ratio_all_width (k := k) x t hDelta

theorem finite_bminus_ratio_all_width (x : Fin n → Fˣ) (τ : F)
    (hDelta : DeltaB x≠0) :
    RedBminus x τ k=(PhiB (k := k) x*VBminus (n := n) (k := k) τ).det/DeltaB x := by
  apply finiteB_from_alternant_all_width (k := k) x (τ^2) hDelta (bminusAlternantColumn τ)
    (fun z => 1+τ*z) (VBminus τ)
  · intro y
    exact lemma_2_1_eq_2_5_of τ (fun a => (y a : F))
  · intro a r
    simpa only [finiteBminusRow,mul_assoc] using finiteBminusRow_column_all_width (k := k) x τ a r

theorem finite_bminus_ratio (x : Fin n → Fˣ) (τ : F) (_hk : 0<k)
    (hDelta : DeltaB x≠0) :
    RedBminus x τ k=(PhiB (k := k) x*VBminus (n := n) (k := k) τ).det/DeltaB x := finite_bminus_ratio_all_width (k := k) x τ hDelta

theorem finite_bc_ratio_all_width (x : Fin n → Fˣ) (τ : F)
    (hDelta : DeltaC x≠0) :
    RedBC x τ k=(PhiC (k := k) x*VBC (n := n) (k := k) τ).det/DeltaC x := by
  apply finiteC_from_alternant_all_width (k := k) x (τ^2) hDelta (fun r z => (1+τ*z)*fColumn (τ^2) r z)
    (fun z => 1+τ*z) (VBC τ)
  · intro y
    have h := det_mul_column (fun a => 1+τ*(y a : F))
      (Matrix.of fun a r : Fin n => fColumn (τ^2) r (y a : F))
    rw [lemma_2_1_eq_2_3_of (τ^2) _] at h
    exact h
  · intro a r
    have h := finiteBCRow_column_all_width (k := k) x τ a r
    simp only [finiteBasicRow,
      show -((n:ℤ)-1)-((k:ℤ)+1)= -(n:ℤ)-(k:ℤ) by ring] at h
    convert h using 1
    ring

theorem finite_bc_ratio (x : Fin n → Fˣ) (τ : F) (_hk : 0<k)
    (hDelta : DeltaC x≠0) :
    RedBC x τ k=(PhiC (k := k) x*VBC (n := n) (k := k) τ).det/DeltaC x := finite_bc_ratio_all_width (k := k) x τ hDelta

theorem finite_bt_ratio_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaB x≠0) :
    RedBt x t k=(PhiB (k := k) x*VBt (n := n) (k := k) t).det/DeltaB x := by
  apply finiteB_from_alternant_all_width (k := k) x t hDelta (fun r z => (1-t*z)*fColumn t r z)
    (fun z => 1-t*z) (VBt t)
  · intro y
    have h := det_mul_column (fun a => 1-t*(y a : F))
      (Matrix.of fun a r : Fin n => fColumn t r (y a : F))
    rw [lemma_2_1_eq_2_3_of t _] at h
    exact h
  · intro a r
    have h := finiteBtRow_column_all_width (k := k) x t a r
    simp only [finiteBasicRow,
      show -((n:ℤ)-1)-(k:ℤ)= -(n:ℤ)+1-(k:ℤ) by ring] at h
    convert h using 1
    ring

theorem finite_bt_ratio (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaB x≠0) :
    RedBt x t k=(PhiB (k := k) x*VBt (n := n) (k := k) t).det/DeltaB x := finite_bt_ratio_all_width (k := k) x t hDelta

end
end AffineDualJT
