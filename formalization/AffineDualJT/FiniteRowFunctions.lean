import AffineDualJT.FiniteColumnEvaluation

/-! # Laurent row functions and the three finite foldings, source.tex §2.2 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- The basic weighted alternant row, with an integer weight for shifted columns. -/
def finiteBasicRow (t : F) (j : ℤ) (r : Fin n) (z : F) : F :=
  z^(-((n:ℤ)-1)-j)*fColumn t r z

theorem finiteBasicRow_apply (t z : F) (hz : z≠0) (j : ℤ) (r : Fin n) :
    finiteBasicRow t j r z = if r.val=0 then z^(-j) else
      z^(-j-(r.val:ℤ))+t^r.val*z^((r.val:ℤ)-j) := by
  have hr := r.isLt
  by_cases hr0 : r.val=0
  · simp only [finiteBasicRow,fColumn,hr0,ite_true,← zpow_natCast z]
    rw [← zpow_add₀ hz]
    congr 1
    omega
  · simp only [finiteBasicRow,fColumn,hr0,ite_false,mul_add,← zpow_natCast z]
    rw [mul_left_comm (z^(-((n:ℤ)-1)-j)) (t^r.val),
      ← zpow_add₀ hz,← zpow_add₀ hz]
    rw [show -((n:ℤ)-1)-j+((n-(r.val+1):ℕ):ℤ)= -j-(r.val:ℤ) by omega,
      show -((n:ℤ)-1)-j+((n+r.val-1:ℕ):ℤ)=(r.val:ℤ)-j by omega]

theorem finiteBasicRow_mul_z (t z : F) (hz : z≠0) (j : ℤ) (r : Fin n) :
    z*finiteBasicRow t j r z = finiteBasicRow t (j-1) r z := by
  unfold finiteBasicRow
  rw [← mul_assoc]
  have h : z*z^(-((n:ℤ)-1)-j)=z^(-((n:ℤ)-1)-(j-1)) := by
    calc
      _ = z^(1+(-((n:ℤ)-1)-j)) := by rw [zpow_add₀ hz,zpow_one]
      _ = _ := by congr 1; ring
  rw [h]

theorem z_mul_inv_zpow (z : F) (hz : z≠0) (m : ℤ) :
    z*(z⁻¹)^m=z^(1-m) := by
  rw [_root_.inv_zpow,← _root_.zpow_neg]
  calc
    _ = z^(1+(-m)) := by rw [zpow_add₀ hz,zpow_one]
    _ = _ := by congr 1

theorem finiteBasicRow_foldC (t z : F) (hz : z≠0) (j : ℤ) (r : Fin n) :
    finiteBasicRow t j r z-finiteBasicRow t j r z⁻¹ =
      -(if r.val=0 then phi j z else
        phi (j+(r.val:ℤ)) z+t^r.val*phi (j-(r.val:ℤ)) z) := by
  rw [finiteBasicRow_apply t z hz,finiteBasicRow_apply t z⁻¹ (inv_ne_zero hz)]
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true,phi,_root_.inv_zpow,← _root_.zpow_neg,neg_neg]
    ring
  · simp only [hr0,ite_false,phi,_root_.inv_zpow,← _root_.zpow_neg,neg_neg]
    rw [show -(-j-(r.val:ℤ))=j+(r.val:ℤ) by ring,
      show -((r.val:ℤ)-j)=j-(r.val:ℤ) by ring,
      show -(j+(r.val:ℤ))= -j-(r.val:ℤ) by ring,
      show -(j-(r.val:ℤ))=(r.val:ℤ)-j by ring]
    ring

theorem finiteBasicRow_foldB (t z : F) (hz : z≠0) (j : ℤ) (r : Fin n) :
    finiteBasicRow t j r z-z*finiteBasicRow t j r z⁻¹ =
      -(if r.val=0 then psi (j+1) z else
        psi (j+(r.val:ℤ)+1) z+t^r.val*psi (j+1-(r.val:ℤ)) z) := by
  rw [finiteBasicRow_apply t z hz,finiteBasicRow_apply t z⁻¹ (inv_ne_zero hz)]
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true,psi]
    rw [z_mul_inv_zpow z hz,
      show 1-(-j)=j+1 by ring,show 1-(j+1)= -j by ring]
    ring
  · simp only [hr0,ite_false,psi,mul_add]
    rw [mul_left_comm z (t^r.val),z_mul_inv_zpow z hz,z_mul_inv_zpow z hz]
    rw [show 1-(-j-(r.val:ℤ))=j+(r.val:ℤ)+1 by ring,
      show 1-((r.val:ℤ)-j)=j+1-(r.val:ℤ) by ring,
      show 1-(j+(r.val:ℤ)+1)= -j-(r.val:ℤ) by ring,
      show 1-(j+1-(r.val:ℤ))=(r.val:ℤ)-j by ring]
    ring

/-- The basic `C` row folds to minus the evaluated `u^C` column. -/
theorem finiteBasicRow_C_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)+1) r (x a : F)-
      finiteBasicRow t ((k:ℤ)+1) r (x a : F)⁻¹ =
        -(PhiC (k := k) x*VC0 (n := n) (k := k) t) a r := by
  rw [finiteBasicRow_foldC t _ (Units.ne_zero _),Matrix.mul_apply]
  simp only [VC0]
  rw [PhiC_uC_apply_all_width (k := k) x t]
  congr 1
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true]
  · simp only [hr0,ite_false,paperIndex]
    congr 2 <;> ring_nf

/-- The basic shifted `B` row folds to minus the evaluated `u^B` column. -/

theorem finiteBasicRow_C_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)+1) r (x a : F)-
      finiteBasicRow t ((k:ℤ)+1) r (x a : F)⁻¹ =
        -(PhiC (k := k) x*VC0 (n := n) (k := k) t) a r := finiteBasicRow_C_column_all_width (k := k) x t a r

theorem finiteBasicRow_B_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t (k:ℤ) r (x a : F)-
      (x a : F)*finiteBasicRow t (k:ℤ) r (x a : F)⁻¹ =
        -(PhiB (k := k) x*VB0 (n := n) (k := k) t) a r := by
  rw [finiteBasicRow_foldB t _ (Units.ne_zero _),Matrix.mul_apply]
  simp only [VB0]
  rw [PhiB_uB_apply_all_width (k := k) x t]
  congr 1
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true]
  · simp only [hr0,ite_false,paperIndex]
    congr 2 <;> ring_nf

theorem finiteBasicRow_B_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t (k:ℤ) r (x a : F)-
      (x a : F)*finiteBasicRow t (k:ℤ) r (x a : F)⁻¹ =
        -(PhiB (k := k) x*VB0 (n := n) (k := k) t) a r := finiteBasicRow_B_column_all_width (k := k) x t a r

theorem finiteBasicRow_C_tilde_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)) r (x a : F)-
      finiteBasicRow t ((k:ℤ)) r (x a : F)⁻¹ =
        -(∑ p : Fin (n+k), PhiC x a p*uCTilde (n := n) (k := k) t r p) := by
  rw [finiteBasicRow_foldC t _ (Units.ne_zero _),PhiC_uCTilde_apply_all_width (k := k) x t]
  congr 1
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true]
    congr 1
  · simp only [hr0,ite_false,paperIndex]
    congr 2 <;> ring_nf

theorem finiteBasicRow_C_tilde_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)) r (x a : F)-
      finiteBasicRow t ((k:ℤ)) r (x a : F)⁻¹ =
        -(∑ p : Fin (n+k), PhiC x a p*uCTilde (n := n) (k := k) t r p) := finiteBasicRow_C_tilde_column_all_width (k := k) x t a r

theorem finiteBasicRow_B_tilde_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)-1) r (x a : F)-
      (x a : F)*finiteBasicRow t ((k:ℤ)-1) r (x a : F)⁻¹ =
        -(∑ p : Fin (n+k), PhiB x a p*uBTilde (n := n) (k := k) t r p) := by
  rw [finiteBasicRow_foldB t _ (Units.ne_zero _),PhiB_uBTilde_apply_all_width (k := k) x t]
  congr 1
  by_cases hr0 : r.val=0
  · simp only [hr0,ite_true]
    congr 1
    ring
  · simp only [hr0,ite_false,paperIndex]
    congr 2 <;> ring_nf

theorem finiteBasicRow_B_tilde_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteBasicRow t ((k:ℤ)-1) r (x a : F)-
      (x a : F)*finiteBasicRow t ((k:ℤ)-1) r (x a : F)⁻¹ =
        -(∑ p : Fin (n+k), PhiB x a p*uBTilde (n := n) (k := k) t r p) := finiteBasicRow_B_tilde_column_all_width (k := k) x t a r

theorem finiteBCRow_column_all_width (x : Fin n → Fˣ) (τ : F)
    (a : Fin n) (r : Fin n) :
    (1+τ*(x a : F))*finiteBasicRow (τ^2) ((k:ℤ)+1) r (x a : F)-
      (1+τ*(x a : F)⁻¹)*finiteBasicRow (τ^2) ((k:ℤ)+1) r (x a : F)⁻¹ =
        -(PhiC (k := k) x*VBC (n := n) (k := k) τ) a r := by
  have hmain := finiteBasicRow_C_column_all_width (k := k) x (τ^2) a r
  have htilde := finiteBasicRow_C_tilde_column_all_width (k := k) x (τ^2) a r
  have hz := finiteBasicRow_mul_z (τ^2) (x a : F) (Units.ne_zero _) ((k:ℤ)+1) r
  have hi := finiteBasicRow_mul_z (τ^2) (x a : F)⁻¹ (inv_ne_zero (Units.ne_zero _)) ((k:ℤ)+1) r
  rw [show (k:ℤ)+1-1=(k:ℤ) by ring] at hz hi
  rw [← hz,← hi] at htilde
  rw [Matrix.mul_apply] at hmain ⊢
  simp only [VC0] at hmain
  simp only [VBC]
  rw [finite_column_pairing]
  linear_combination hmain+τ*htilde

theorem finiteBCRow_column (x : Fin n → Fˣ) (τ : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (1+τ*(x a : F))*finiteBasicRow (τ^2) ((k:ℤ)+1) r (x a : F)-
      (1+τ*(x a : F)⁻¹)*finiteBasicRow (τ^2) ((k:ℤ)+1) r (x a : F)⁻¹ =
        -(PhiC (k := k) x*VBC (n := n) (k := k) τ) a r := finiteBCRow_column_all_width (k := k) x τ a r

theorem finiteBtRow_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    (1-t*(x a : F))*finiteBasicRow t (k:ℤ) r (x a : F)-
      (x a : F)*(1-t*(x a : F)⁻¹)*finiteBasicRow t (k:ℤ) r (x a : F)⁻¹ =
        -(PhiB (k := k) x*VBt (n := n) (k := k) t) a r := by
  have hmain := finiteBasicRow_B_column_all_width (k := k) x t a r
  have htilde := finiteBasicRow_B_tilde_column_all_width (k := k) x t a r
  have hz := finiteBasicRow_mul_z t (x a : F) (Units.ne_zero _) (k:ℤ) r
  have hi := finiteBasicRow_mul_z t (x a : F)⁻¹ (inv_ne_zero (Units.ne_zero _)) (k:ℤ) r
  rw [← hz,← hi] at htilde
  rw [Matrix.mul_apply] at hmain ⊢
  simp only [VB0] at hmain
  simp only [VBt,sub_eq_add_neg,← neg_mul]
  rw [finite_column_pairing]
  linear_combination hmain-t*htilde

theorem finiteBtRow_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    (1-t*(x a : F))*finiteBasicRow t (k:ℤ) r (x a : F)-
      (x a : F)*(1-t*(x a : F)⁻¹)*finiteBasicRow t (k:ℤ) r (x a : F)⁻¹ =
        -(PhiB (k := k) x*VBt (n := n) (k := k) t) a r := finiteBtRow_column_all_width (k := k) x t a r

def finiteCtRow (t : F) (k : ℕ) (r : Fin n) (z : F) : F :=
  z^(-(n:ℤ)-(k:ℤ))*ctAlternantColumn t r z

def finiteBminusRow (τ : F) (k : ℕ) (r : Fin n) (z : F) : F :=
  z^(-(n:ℤ)+1-(k:ℤ))*bminusAlternantColumn τ r z

theorem finiteCtRow_apply (t z : F) (hz : z≠0) (r : Fin n) :
    finiteCtRow t k r z = z^(-(k:ℤ)-(r.val:ℤ)-1)-
      t^(r.val+1)*z^((r.val:ℤ)+1-(k:ℤ)) := by
  have hr := r.isLt
  simp only [finiteCtRow,ctAlternantColumn,mul_sub,← zpow_natCast z]
  rw [mul_left_comm (z^(-(n:ℤ)-(k:ℤ))) (t^(r.val+1)),
    ← zpow_add₀ hz,← zpow_add₀ hz]
  rw [show -(n:ℤ)-(k:ℤ)+((n-(r.val+1):ℕ):ℤ)= -(k:ℤ)-(r.val:ℤ)-1 by omega,
    show -(n:ℤ)-(k:ℤ)+((n+r.val+1:ℕ):ℤ)=(r.val:ℤ)+1-(k:ℤ) by omega]

theorem finiteBminusRow_apply (τ z : F) (hz : z≠0) (r : Fin n) :
    finiteBminusRow τ k r z = z^(-(k:ℤ)-(r.val:ℤ))+
      τ^(2*r.val+1)*z^((r.val:ℤ)+1-(k:ℤ)) := by
  have hr := r.isLt
  simp only [finiteBminusRow,bminusAlternantColumn,mul_add,← zpow_natCast z]
  rw [mul_left_comm (z^(-(n:ℤ)+1-(k:ℤ))) (τ^(2*r.val+1)),
    ← zpow_add₀ hz,← zpow_add₀ hz]
  rw [show -(n:ℤ)+1-(k:ℤ)+((n-(r.val+1):ℕ):ℤ)= -(k:ℤ)-(r.val:ℤ) by omega,
    show -(n:ℤ)+1-(k:ℤ)+((n+r.val:ℕ):ℤ)=(r.val:ℤ)+1-(k:ℤ) by omega]

theorem finiteCtRow_column_all_width (x : Fin n → Fˣ) (t : F)
    (a : Fin n) (r : Fin n) :
    finiteCtRow t k r (x a : F)-finiteCtRow t k r (x a : F)⁻¹ =
      -(PhiC (k := k) x*VCt (n := n) (k := k) t) a r := by
  rw [finiteCtRow_apply t _ (Units.ne_zero _),
    finiteCtRow_apply t _ (inv_ne_zero (Units.ne_zero _)),PhiC_VCt_apply_all_width (k := k) x t]
  simp only [phi,paperIndex,_root_.inv_zpow,← _root_.zpow_neg]
  rw [show -(-(k:ℤ)-(r.val:ℤ)-1)=(k:ℤ)+(r.val:ℤ)+1 by ring,
    show -((r.val:ℤ)+1-(k:ℤ))=(k:ℤ)-(r.val:ℤ)-1 by ring,
    show (k:ℤ)+((r.val:ℤ)+1)=(k:ℤ)+(r.val:ℤ)+1 by ring,
    show (k:ℤ)-((r.val:ℤ)+1)=(k:ℤ)-(r.val:ℤ)-1 by ring,
    show -((k:ℤ)+(r.val:ℤ)+1)= -(k:ℤ)-(r.val:ℤ)-1 by ring,
    show -((k:ℤ)-(r.val:ℤ)-1)=(r.val:ℤ)+1-(k:ℤ) by ring]
  ring

theorem finiteCtRow_column (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteCtRow t k r (x a : F)-finiteCtRow t k r (x a : F)⁻¹ =
      -(PhiC (k := k) x*VCt (n := n) (k := k) t) a r := finiteCtRow_column_all_width (k := k) x t a r

theorem finiteBminusRow_column_all_width (x : Fin n → Fˣ) (τ : F)
    (a : Fin n) (r : Fin n) :
    finiteBminusRow τ k r (x a : F)-
      (x a : F)*finiteBminusRow τ k r (x a : F)⁻¹ =
      -(PhiB (k := k) x*VBminus (n := n) (k := k) τ) a r := by
  rw [finiteBminusRow_apply τ _ (Units.ne_zero _),
    finiteBminusRow_apply τ _ (inv_ne_zero (Units.ne_zero _)),PhiB_VBminus_apply_all_width (k := k) x τ]
  simp only [psi,paperIndex,mul_add]
  rw [mul_left_comm (x a : F) (τ^(2*r.val+1)),
    z_mul_inv_zpow _ (Units.ne_zero _),z_mul_inv_zpow _ (Units.ne_zero _)]
  rw [show 1-(-(k:ℤ)-(r.val:ℤ))=(k:ℤ)+(r.val:ℤ)+1 by ring,
    show 1-((r.val:ℤ)+1-(k:ℤ))=(k:ℤ)-(r.val:ℤ) by ring,
    show (k:ℤ)+((r.val:ℤ)+1)=(k:ℤ)+(r.val:ℤ)+1 by ring,
    show (k:ℤ)+1-((r.val:ℤ)+1)=(k:ℤ)-(r.val:ℤ) by ring,
    show 1-((k:ℤ)+(r.val:ℤ)+1)= -(k:ℤ)-(r.val:ℤ) by ring,
    show 1-((k:ℤ)-(r.val:ℤ))=(r.val:ℤ)+1-(k:ℤ) by ring]
  ring

theorem finiteBminusRow_column (x : Fin n → Fˣ) (τ : F) (_hk : 0<k)
    (a : Fin n) (r : Fin n) :
    finiteBminusRow τ k r (x a : F)-
      (x a : F)*finiteBminusRow τ k r (x a : F)⁻¹ =
      -(PhiB (k := k) x*VBminus (n := n) (k := k) τ) a r := finiteBminusRow_column_all_width (k := k) x τ a r

end
end AffineDualJT
