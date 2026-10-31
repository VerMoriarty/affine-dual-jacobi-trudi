import AffineDualJT.OrdinaryBColumnKernels
import AffineDualJT.OrdinaryIdentityTransfer
import AffineDualJT.WeightExponents
import AffineDualJT.ParameterPolynomials
import AffineDualJT.FieldEmbedding

/-! # Proposition 4.2: the ordinary B0 and B- affine identities -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem DB_CB_B0_pairing (x : Fin n → Fˣ) (t : F) (i j : Fin k) :
    ((DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (bB0Seq t)) i j=
      ∑ᶠ y : ℤ, ((-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))*
        hKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+1)*y) := by
  rw [lemma_3_3_eq_3_6]
  change (∑ᶠ m : ℤ, hKernel (classicalCoefficients x) i m*
    (∑ᶠ y : ℤ, if m=paperIndex j-(2*(k:ℤ)+1)*y then
      (-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2) else 0))=_
  simpa only [mul_comm] using residueSum_minus_pairing (2*(k:ℤ)+1) (paperIndex j)
    (by omega) (hKernel (classicalCoefficients x) i)
    (fun y => (-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))

theorem DB_CB_Bminus_pairing (x : Fin n → Fˣ) (τ : F) (hk : 0<k) (i j : Fin k) :
    ((DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (bBminusSeq τ)) i j=
      ∑ᶠ y : ℤ, τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y)*
        hKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
  rw [lemma_3_3_eq_3_6]
  change (∑ᶠ m : ℤ, hKernel (classicalCoefficients x) i m*
    (∑ᶠ y : ℤ, if m=paperIndex j-2*(k:ℤ)*y then
      τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y) else 0))=_
  simpa only [mul_comm] using residueSum_minus_pairing (2*(k:ℤ)) (paperIndex j)
    (by omega) (hKernel (classicalCoefficients x) i)
    (fun y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))

theorem ordinary_B0_nonzero [CharZero F] (x : Fin n → Fˣ) (t : F) (ht : t≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedB0 x t k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (hKernel (classicalCoefficients x)) := by
  rw [prop_2_2_B0 x t hn hk hDelta]
  have h := ordinary_B_transfer x (VB0 t) (bB0Seq t) (VB0_transpose_CB t ht hk)
    hDelta (prop_2_2_minor_VB0 t hk) (CB_B0_head t)
  have hm : (DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (bB0Seq t)=
      Matrix.of fun i j : Fin k => ∑ᶠ y : ℤ,
        ((-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))*
          hKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+1)*y) := by
    ext i j
    exact DB_CB_B0_pairing x t i j
  rw [hm] at h
  refine h.trans ?_
  exact det_finsum_eq_JK (2*(k:ℤ)+1) (by omega) _ _ (hKernel_hasFiniteSupport _)

theorem ordinary_Bminus_nonzero (x : Fin n → Fˣ) (τ : F) (hτ : τ≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBminus x τ k=JK (k := k) (2*(k:ℤ))
      (fun j y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (hKernel (classicalCoefficients x)) := by
  rw [prop_2_2_Bminus x τ hn hk hDelta]
  have h := ordinary_B_transfer x (VBminus τ) (bBminusSeq τ) (VBminus_transpose_CB τ hτ hk)
    hDelta (prop_2_2_minor_VBminus τ hk) (CB_Bminus_head τ hk)
  have hm : (DB (k := k) (classicalCoefficients x)).transpose*
      CB (n := n) (k := k) (bBminusSeq τ)=
      Matrix.of fun i j : Fin k => ∑ᶠ y : ℤ,
        τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y)*
          hKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y) := by
    ext i j
    exact DB_CB_Bminus_pairing x τ hk i j
  rw [hm] at h
  refine h.trans ?_
  exact det_finsum_eq_JK (2*(k:ℤ)) (by omega) _ _ (hKernel_hasFiniteSupport _)

theorem B0_weight_zero (j : Fin k) (y : ℤ) (hy : y≠0) :
    (0:F)^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2)=0 := by
  have hk : 0 < k := by have hj := j.isLt; omega
  exact _root_.zero_zpow _ (ne_of_gt (B0_exponent_pos hk j y hy))

/-- The B-minus zero endpoint over an infinite field, specialized from the
nonzero square-root-parameter identity through parameter polynomials. -/
theorem ordinary_Bminus_zero_of_infinite [Infinite F] (x : Fin n → Fˣ)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBminus x 0 k=JK (k := k) (2*(k:ℤ))
      (fun j y => (0:F)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (hKernel (classicalCoefficients x)) := by
  let E (j : Fin k) (y : ℤ) : ℤ := (2*(k:ℤ))*y^2-(2*paperIndex j-1)*y
  have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
    pow_toNat_eq_zpow t _ (Bminus_exponent_nonneg j y)
  have hrho (t z : F) : (1-z)⁻¹+t*(z*(1-z)⁻¹) = (1+t*z)/(1-z) := by
    rw [div_eq_mul_inv]
    ring
  have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)) (by omega)
    2 (by omega) (fun z => (1-z)⁻¹) (fun z => z*(1-z)⁻¹)
    (fun j y => (E j y).toNat) (fun _ _ => (1:F))
    (hKernel (classicalCoefficients x)) (hKernel_hasFiniteSupport _) (1:F)
    (by
      intro t ht
      have ha := ordinary_Bminus_nonzero x t ht hn hk hDelta
      simpa only [RedBminus, hrho, hpow, E, one_mul] using ha)
  simpa only [RedBminus, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul,
    add_zero, one_div, hpow, E, one_mul] using h

/-- Descend the polynomial specialization from the rational-function field,
so the original B-minus theorem remains valid over an arbitrary field. -/
theorem ordinary_Bminus_zero (x : Fin n → Fˣ)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBminus x 0 k=JK (k := k) (2*(k:ℤ))
      (fun j y => (0:F)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (hKernel (classicalCoefficients x)) := by
  let φ : F →+* RatFunc F := RatFunc.C
  let : Infinite (RatFunc F) := Infinite.of_injective
    (algebraMap (Polynomial F) (RatFunc F))
    (IsFractionRing.injective (Polynomial F) (RatFunc F))
  have hDelta' : DeltaB (mapWeylVariables φ x) ≠ 0 := by
    intro hz
    apply hDelta
    apply φ.injective
    simpa only [map_DeltaB, map_zero] using hz
  have hred : φ (RedBminus x 0 k) = RedBminus (mapWeylVariables φ x) 0 k := by
    simpa only [RedBminus, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul,
      add_zero, one_div, map_zero] using
      (map_reducedWeyl φ x 0 k (fun z => (1-z)⁻¹) (fun z => (1-z)⁻¹)
        (by intro z; simp only [map_inv₀, map_sub, map_one]))
  have hsum : φ (JK (k := k) (2*(k:ℤ))
      (fun j y => (0:F)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (hKernel (classicalCoefficients x))) =
      JK (k := k) (2*(k:ℤ))
        (fun j y => (0:RatFunc F)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
        (hKernel (classicalCoefficients (mapWeylVariables φ x))) := by
    rw [map_JK φ _ (by omega) _ _ (hKernel_hasFiniteSupport _)]
    simp only [map_zpow₀, map_zero, map_hKernel]
  apply φ.injective
  rw [hred, hsum]
  exact ordinary_Bminus_zero_of_infinite (mapWeylVariables φ x) hn hk hDelta'

/-- Equation (1.3), including the zero parameter endpoint. -/
theorem ordinary_B0_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedB0 x t k=JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y*t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (hKernel (classicalCoefficients x)) := by
  by_cases ht : t=0
  · subst t
    let E (j : Fin k) (y : ℤ) : ℤ :=
      ((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2
    have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
      pow_toNat_eq_zpow t _ (B0_exponent_nonneg j y)
    have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)+1) (by omega)
      1 (by omega) (fun z => (1-z)⁻¹) (fun _ => 0)
      (fun j y => (E j y).toNat) (fun _ y => (-1:F)^y)
      (hKernel (classicalCoefficients x)) (hKernel_hasFiniteSupport _) (1:F)
      (by
        intro t ht
        have ha := ordinary_B0_nonzero x t ht hn hk hDelta
        simpa only [RedB0, pow_one, mul_zero, add_zero, one_mul, hpow, E] using ha)
    simpa only [RedB0, one_mul, hpow, E] using h
  · exact ordinary_B0_nonzero x t ht hn hk hDelta

/-- Equation (1.4), with the square-root parameter and its zero endpoint. -/
theorem ordinary_Bminus_identity (x : Fin n → Fˣ) (τ : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x≠0) :
    RedBminus x τ k=JK (k := k) (2*(k:ℤ))
      (fun j y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (hKernel (classicalCoefficients x)) := by
  by_cases hτ : τ=0
  · subst τ
    exact ordinary_Bminus_zero x hn hk hDelta
  · exact ordinary_Bminus_nonzero x τ hτ hn hk hDelta

end
end AffineDualJT
