import AffineDualJT.ExceptionalBplusKernels
import AffineDualJT.OrdinaryIdentityTransfer
import AffineDualJT.WeightExponents
import AffineDualJT.ParameterPolynomials

/-! # Proposition 5.3: the fixed-center B+ affine identity -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem DPlus_CPlus_Bplus_pairing (x : Fin n → Fˣ) (t : F) (hk : 0<k) (i j : Fin k) :
    ((DPlus (k := k) (classicalCoefficients x)).transpose*
      CPlus (n := n) (k := k) (bBplus t)) i j=
      ∑ᶠ y : ℤ, ((-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))*
        hPlusKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
  rw [lemma_3_3_eq_3_7]
  change (∑ᶠ m : ℤ, hPlusKernel (classicalCoefficients x) i m*
    (∑ᶠ y : ℤ, if m=paperIndex j-2*(k:ℤ)*y then
      (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y) else 0))=_
  simpa only [mul_comm] using residueSum_minus_pairing (2*(k:ℤ)) (paperIndex j)
    (by omega) (hPlusKernel (classicalCoefficients x) i)
    (fun y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))

theorem exceptional_Bplus_nonzero [CharZero F] (x : Fin n → Fˣ) (t : F) (ht : t≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x≠0) :
    RedBplus x t k=(2:F)⁻¹*JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (hPlusKernel (classicalCoefficients x)) := by
  classical
  have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hζ : zetaSign F n k≠0 := mul_ne_zero hs hω
  rw [prop_2_2_Bplus x t hn hk hDelta]
  have htr := normalized_transfer_3_1 (PhiPlus (k := k) x) (VBplus t)
    (DPlus (k := k) (classicalCoefficients x)) (CPlus (n := n) (k := k) (bBplus t))
    (lemma_3_2_PhiPlus_DPlus x) (VBplus_transpose_CPlus t ht hk) hDelta
    (by rw [lemma_3_2_minor_DPlus x hk]; exact mul_ne_zero (by norm_num) hζ)
    (prop_2_2_minor_VBplus t hk) (by rw [CPlus_Bplus_head t hk]; exact hω)
  rw [lemma_3_2_minor_DPlus x hk,CPlus_Bplus_head t hk] at htr
  unfold zetaSign at htr
  have hden : (2*((-1:F)^(n*k)*omegaSign F k))*omegaSign F k=2*(-1:F)^(n*k) := by
    calc
      _ = 2*(-1:F)^(n*k)*(omegaSign F k*omegaSign F k) := by ring
      _ = _ := by rw [omegaSign_mul_self,mul_one]
  have hcoeff : (-1:F)^(n*k)/(2*(-1:F)^(n*k))=(2:F)⁻¹ := by field_simp
  rw [hden,hcoeff] at htr
  have hm : (DPlus (k := k) (classicalCoefficients x)).transpose*
      CPlus (n := n) (k := k) (bBplus t)=
      Matrix.of fun i j : Fin k => ∑ᶠ y : ℤ,
        ((-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))*
          hPlusKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
    ext i j
    exact DPlus_CPlus_Bplus_pairing x t hk i j
  rw [hm] at htr
  refine htr.trans ?_
  exact congrArg (fun z : F => (2:F)⁻¹*z)
    (det_finsum_eq_JK (2*(k:ℤ)) (by omega) _ _ (hPlusKernel_hasFiniteSupport _))

theorem Bplus_weight_zero (j : Fin k) (y : ℤ) (hy : y≠0) :
    (0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y)=0 := by
  have hk : 0 < k := by have hj := j.isLt; omega
  exact _root_.zero_zpow _ (ne_of_gt (Bplus_Bt_exponent_pos hk j y hy))

/-- Equation (1.5); the factor `1/2` comes from the doubled coefficient minor. -/
theorem exceptional_Bplus_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x≠0) :
    RedBplus x t k=(2:F)⁻¹*JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (hPlusKernel (classicalCoefficients x)) := by
  by_cases ht : t=0
  · subst t
    let E (j : Fin k) (y : ℤ) : ℤ := (k:ℤ)*y^2-(paperIndex j-1)*y
    have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
      pow_toNat_eq_zpow t _ (Bplus_Bt_exponent_nonneg j y)
    have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)) (by omega)
      1 (by omega) (fun _ => 1) (fun _ => 0)
      (fun j y => (E j y).toNat) (fun _ y => (-1:F)^y)
      (hPlusKernel (classicalCoefficients x)) (hPlusKernel_hasFiniteSupport _) ((2:F)⁻¹)
      (by
        intro t ht
        have ha := exceptional_Bplus_nonzero x t ht hn hk hDelta
        simpa only [RedBplus, pow_one, mul_zero, add_zero, hpow, E] using ha)
    simpa only [RedBplus, hpow, E] using h
  · exact exceptional_Bplus_nonzero x t ht hn hk hDelta

end
end AffineDualJT
