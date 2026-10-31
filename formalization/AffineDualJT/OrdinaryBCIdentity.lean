import AffineDualJT.OrdinaryBCColumnKernels
import AffineDualJT.OrdinaryIdentityTransfer
import AffineDualJT.WeightExponents
import AffineDualJT.ParameterPolynomials
import AffineDualJT.FieldEmbedding

/-! # Proposition 4.1, the ordinary BC identity -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- The odd residue period contributes the affine sign `(-1)^y`. -/
theorem DC_CC_BC_pairing (x : Fin n → Fˣ) (τ : F) (i j : Fin k) :
    ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bBCSeq τ)) i j=
      (-1:F)^(j.val+1)*(∑ᶠ y : ℤ,
        ((-1:F)^y*τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))*
          lambdaKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+1)*y)) := by
  rw [lemma_3_3_eq_3_5]
  have h := residueSum_pairing (2*(k:ℤ)+1) (paperIndex j) (by omega)
    (fun m => (-1:F)^m*lambdaKernel (classicalCoefficients x) i m)
    (fun q => τ^((2*(k:ℤ)+1)*q^2+2*paperIndex j*q))
  change (∑ᶠ m : ℤ, ((-1:F)^m*lambdaKernel (classicalCoefficients x) i m)*
    residueSum (2*(k:ℤ)+1) (paperIndex j)
      (fun q => τ^((2*(k:ℤ)+1)*q^2+2*paperIndex j*q)) m)=_ at ⊢
  rw [h,← finsum_comp_equiv (Equiv.neg ℤ),mul_finsum]
  apply finsum_congr
  intro y
  simp only [Equiv.neg_apply]
  have hs : (-1:F)^((2*(k:ℤ)+1)*(-y))=(-1:F)^y := by
    rw [show (2*(k:ℤ)+1)*(-y)=2*((k:ℤ)*(-y))+(-y) by ring,
      zpow_add₀ (by norm_num : (-1:F)≠0),(even_two_mul _).neg_one_zpow,one_mul]
    simp only [← Int.cast_negOnePow F,Int.negOnePow_neg]
  rw [zpow_add₀ (by norm_num : (-1:F)≠0),hs]
  rw [show (2*(k:ℤ)+1)*(-y)^2+2*paperIndex j*(-y)=
      (2*(k:ℤ)+1)*y^2-2*paperIndex j*y by ring,
    show paperIndex j+(2*(k:ℤ)+1)*(-y)=paperIndex j-(2*(k:ℤ)+1)*y by ring,
    show paperIndex j=((j.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]
  ring

theorem ordinary_BC_nonzero (x : Fin n → Fˣ) (τ : F) (hτ : τ≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedBC x τ k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  classical
  let A : Matrix (Fin k) (Fin k) F := Matrix.of fun i j =>
    ∑ᶠ y : ℤ, ((-1:F)^y*τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))*
      lambdaKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+1)*y)
  have hζ : zetaSign F n k≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hpair : ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bBCSeq τ)).det=omegaSign F k*A.det := by
    have hm : (DC (k := k) (classicalCoefficients x)).transpose*
        CC (n := n) (k := k) (bBCSeq τ)=
      Matrix.of fun i j => (-1:F)^(j.val+1)*A i j := by
      ext i j
      exact DC_CC_BC_pairing x τ i j
    rw [hm,← prod_first_sign]
    exact det_mul_row _ A
  rw [prop_2_2_BC x τ hn hk hDelta]
  have htr := normalized_transfer_3_1 (PhiC (k := k) x) (VBC τ)
    (DC (k := k) (classicalCoefficients x)) (CC (n := n) (k := k) (bBCSeq τ))
    (lemma_3_2_PhiC_DC x) (VBC_transpose_CC τ hτ hk) hDelta
    (by rw [lemma_3_2_minor_DC]; exact hζ) (prop_2_2_minor_VBC τ hk)
    (by rw [CC_BC_head,det_one]; exact one_ne_zero)
  rw [lemma_3_2_minor_DC,CC_BC_head,det_one,hpair] at htr
  change (PhiC (k := k) x*VBC τ).det/DeltaC x=_ at htr
  have he : (PhiC (k := k) x*VBC τ).det/DeltaC x=A.det := by
    rw [htr]
    unfold zetaSign
    have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
    field_simp
  refine he.trans ?_
  exact det_finsum_eq_JK (2*(k:ℤ)+1) (by omega) _ _ (lambdaKernel_hasFiniteSupport _)

/-- The BC zero endpoint over an infinite field follows by specializing the
nonzero square-root-parameter identity as a polynomial in that parameter. -/
theorem ordinary_BC_zero_of_infinite [Infinite F] (x : Fin n → Fˣ)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedBC x 0 k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*(0:F)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  let E (j : Fin k) (y : ℤ) : ℤ := (2*(k:ℤ)+1)*y^2-2*paperIndex j*y
  have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
    pow_toNat_eq_zpow t _ (BC_exponent_nonneg j y)
  have hrho (t z : F) : (1-z^2)⁻¹+t*(z*(1-z^2)⁻¹) = (1+t*z)/(1-z^2) := by
    rw [div_eq_mul_inv]
    ring
  have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)+1) (by omega)
    2 (by omega) (fun z => (1-z^2)⁻¹) (fun z => z*(1-z^2)⁻¹)
    (fun j y => (E j y).toNat) (fun _ y => (-1:F)^y)
    (lambdaKernel (classicalCoefficients x)) (lambdaKernel_hasFiniteSupport _) (1:F)
    (by
      intro t ht
      have ha := ordinary_BC_nonzero x t ht hn hk hDelta
      simpa only [RedBC, hrho, hpow, E, one_mul] using ha)
  simpa only [RedBC, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul,
    add_zero, one_div, hpow, E, one_mul] using h

/-- Descend the parameter-polynomial specialization from an infinite field
extension, without imposing an extra hypothesis on the original field. -/
theorem ordinary_BC_zero (x : Fin n → Fˣ)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedBC x 0 k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*(0:F)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  let φ : F →+* RatFunc F := RatFunc.C
  let : Infinite (RatFunc F) := Infinite.of_injective
    (algebraMap (Polynomial F) (RatFunc F))
    (IsFractionRing.injective (Polynomial F) (RatFunc F))
  have hDelta' : DeltaC (mapWeylVariables φ x) ≠ 0 := by
    intro hz
    apply hDelta
    apply φ.injective
    simpa only [map_DeltaC, map_zero] using hz
  have hred : φ (RedBC x 0 k) = RedBC (mapWeylVariables φ x) 0 k := by
    simpa only [RedBC, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul,
      add_zero, one_div, map_zero] using
      (map_reducedWeyl φ x 0 k (fun z => (1-z^2)⁻¹) (fun z => (1-z^2)⁻¹)
        (by intro z; simp only [map_inv₀, map_sub, map_one, map_pow]))
  have hsum : φ (JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*(0:F)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (lambdaKernel (classicalCoefficients x))) =
      JK (k := k) (2*(k:ℤ)+1)
        (fun j y => (-1:RatFunc F)^y*(0:RatFunc F)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
        (lambdaKernel (classicalCoefficients (mapWeylVariables φ x))) := by
    rw [map_JK φ _ (by omega) _ _ (lambdaKernel_hasFiniteSupport _)]
    simp only [map_mul, map_zpow₀, map_neg, map_one, map_zero, map_lambdaKernel]
  apply φ.injective
  rw [hred, hsum]
  exact ordinary_BC_zero_of_infinite (mapWeylVariables φ x) hn hk hDelta'

/-- Equation (1.8), including the zero square-root parameter. -/
theorem ordinary_BC_identity (x : Fin n → Fˣ) (τ : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedBC x τ k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  by_cases hτ : τ=0
  · subst τ
    exact ordinary_BC_zero x hn hk hDelta
  · exact ordinary_BC_nonzero x τ hτ hn hk hDelta

end
end AffineDualJT
