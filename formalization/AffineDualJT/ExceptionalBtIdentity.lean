import AffineDualJT.ExceptionalBtKernels
import AffineDualJT.ExceptionalBplusIdentity

/-! # Proposition 5.5: adjacent residues and the Bt affine identity -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- Move the adjacent shift from the residue sequence to the finite kernel. -/
theorem finsum_adjacent_pairing (H b : ℤ → F) (hH : Function.HasFiniteSupport H) :
    (∑ᶠ m : ℤ, H m*(b m+b (m+1)))=
      ∑ᶠ m : ℤ, (H m+H (m-1))*b m := by
  have hHprev : Function.HasFiniteSupport (fun m : ℤ => H (m-1)) :=
    hH.fun_comp_of_injective (by intro a b h; dsimp at h; omega)
  have hA : Function.HasFiniteSupport (fun m => H m*b m) := hH.mul_left b
  have hB : Function.HasFiniteSupport (fun m => H m*b (m+1)) := hH.mul_left _
  have hC : Function.HasFiniteSupport (fun m => H (m-1)*b m) := hHprev.mul_left b
  simp only [mul_add,add_mul]
  rw [finsum_add_distrib hA hB,finsum_add_distrib hA hC]
  congr 1
  rw [← finsum_comp_equiv (Equiv.addRight (-1:ℤ))]
  apply finsum_congr
  intro m
  simp only [Equiv.coe_addRight]
  rw [show m+(-1)=m-1 by ring,sub_add_cancel]

theorem DB_CB_Bt_pairing (x : Fin n → Fˣ) (t : F) (hk : 0<k) (i j : Fin k) :
    ((DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (aBt t)) i j=
      ∑ᶠ y : ℤ, ((-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))*
        hHatKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
  rw [lemma_3_3_eq_3_6]
  simp only [aBt]
  rw [finsum_adjacent_pairing _ _ (hKernel_hasFiniteSupport _ i)]
  simp only [← hHat_eq_h_add_shift]
  change (∑ᶠ m : ℤ, hHatKernel (classicalCoefficients x) i m*
    (∑ᶠ y : ℤ, if m=paperIndex j-2*(k:ℤ)*y then
      (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y) else 0))=_
  simpa only [mul_comm] using residueSum_minus_pairing (2*(k:ℤ)) (paperIndex j)
    (by omega) (hHatKernel (classicalCoefficients x) i)
    (fun y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))

theorem exceptional_Bt_nonzero [CharZero F] (x : Fin n → Fˣ) (t : F) (ht : t≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBt x t k=(2:F)⁻¹*JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (hHatKernel (classicalCoefficients x)) := by
  classical
  have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hζ : zetaSign F n k≠0 := mul_ne_zero hs hω
  rw [prop_2_2_Bt x t hn hk hDelta]
  have htr := normalized_transfer_3_1 (PhiB (k := k) x) (VBt t)
    (DB (k := k) (classicalCoefficients x)) (CB (n := n) (k := k) (aBt t))
    (lemma_3_2_PhiB_DB x) (VBt_transpose_CB t ht hk) hDelta
    (by rw [lemma_3_2_minor_DB]; exact hζ) (prop_2_2_minor_VBt t hk)
    (by rw [CB_Bt_head t hk]; exact mul_ne_zero (by norm_num) hω)
  rw [lemma_3_2_minor_DB,CB_Bt_head t hk] at htr
  unfold zetaSign at htr
  have hden : ((-1:F)^(n*k)*omegaSign F k)*(2*omegaSign F k)=2*(-1:F)^(n*k) := by
    calc
      _ = 2*(-1:F)^(n*k)*(omegaSign F k*omegaSign F k) := by ring
      _ = _ := by rw [omegaSign_mul_self,mul_one]
  have hcoeff : (-1:F)^(n*k)/(2*(-1:F)^(n*k))=(2:F)⁻¹ := by field_simp
  rw [hden,hcoeff] at htr
  have hm : (DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (aBt t)=
      Matrix.of fun i j : Fin k => ∑ᶠ y : ℤ,
        ((-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))*
          hHatKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
    ext i j
    exact DB_CB_Bt_pairing x t hk i j
  rw [hm] at htr
  refine htr.trans ?_
  exact congrArg (fun z : F => (2:F)⁻¹*z)
    (det_finsum_eq_JK (2*(k:ℤ)) (by omega) _ _ (hHatKernel_hasFiniteSupport _))

/-- At `t=0`, every nonzero shift in the `Bt` affine sum has zero weight. -/
theorem Bt_weight_zero (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    (0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y)=0 :=
  Bplus_weight_zero j y hy

/-- The half factor is supplied by the doubled head, including at `t=0`. -/
theorem exceptional_Bt_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBt x t k=(2:F)⁻¹*JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (hHatKernel (classicalCoefficients x)) := by
  by_cases ht : t=0
  · subst t
    let E (j : Fin k) (y : ℤ) : ℤ := (k:ℤ)*y^2-(paperIndex j-1)*y
    have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
      pow_toNat_eq_zpow t _ (Bplus_Bt_exponent_nonneg j y)
    have hrho (t z : F) : (1-z)⁻¹ + t*(-z*(1-z)⁻¹) = (1-t*z)/(1-z) := by
      rw [div_eq_mul_inv]
      ring
    have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)) (by omega)
      1 (by omega) (fun z => (1-z)⁻¹) (fun z => -z*(1-z)⁻¹)
      (fun j y => (E j y).toNat) (fun _ y => (-1:F)^y)
      (hHatKernel (classicalCoefficients x)) (hHatKernel_hasFiniteSupport _) ((2:F)⁻¹)
      (by
        intro t ht
        have ha := exceptional_Bt_nonzero x t ht hn hk hDelta
        simpa only [RedBt, pow_one, hrho, hpow, E] using ha)
    simpa only [RedBt, zero_mul, sub_zero, one_div, hpow, E] using h
  · exact exceptional_Bt_nonzero x t ht hn hk hDelta

end
end AffineDualJT
