import AffineDualJT.OrdinaryColumnKernels
import AffineDualJT.ClassicalSpecialization
import AffineDualJT.WeightExponents
import AffineDualJT.ParameterPolynomials

/-! # Proposition 4.1, the ordinary `C0` identity -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
open AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- The residue pairing in §4.1, including its column sign. -/
theorem DC_CC_C0_pairing (x : Fin n → Fˣ) (t : F) (i j : Fin k) :
    ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bC0Seq t)) i j =
      (-1:F)^(j.val+1)*(∑ᶠ y : ℤ,
        t^(((k:ℤ)+1)*y^2-paperIndex j*y)*
          lambdaKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+2)*y)) := by
  rw [lemma_3_3_eq_3_5]
  have h := residueSum_pairing (2*(k:ℤ)+2) (paperIndex j) (by omega)
    (fun m => (-1:F)^m*lambdaKernel (classicalCoefficients x) i m)
    (fun q => t^(((k:ℤ)+1)*q^2+paperIndex j*q))
  change (∑ᶠ m : ℤ, ((-1:F)^m*lambdaKernel (classicalCoefficients x) i m)*
    residueSum (2*(k:ℤ)+2) (paperIndex j)
      (fun q => t^(((k:ℤ)+1)*q^2+paperIndex j*q)) m)=_ at ⊢
  rw [h,← finsum_comp_equiv (Equiv.neg ℤ),mul_finsum]
  apply finsum_congr
  intro y
  simp only [Equiv.neg_apply]
  have hs : (-1:F)^((2*(k:ℤ)+2)*(-y))=1 := by
    rw [show (2*(k:ℤ)+2)*(-y)=2*(((k:ℤ)+1)*(-y)) by ring]
    exact (even_two_mul _).neg_one_zpow
  rw [zpow_add₀ (by norm_num : (-1:F)≠0),hs,mul_one]
  rw [show ((k:ℤ)+1)*(-y)^2+paperIndex j*(-y)=((k:ℤ)+1)*y^2-paperIndex j*y by ring,
    show paperIndex j+(2*(k:ℤ)+2)*(-y)=paperIndex j-(2*(k:ℤ)+2)*y by ring,
    show paperIndex j=((j.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]
  ring

/-- Complementary transfer and the residue pairing, at a nonzero parameter. -/
theorem ordinary_C0_nonzero [CharZero F] (x : Fin n → Fˣ) (t : F) (ht : t≠0)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedC0 x t k=JK (k := k) (2*(k:ℤ)+2)
      (fun j y => t^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  classical
  let A : Matrix (Fin k) (Fin k) F := Matrix.of fun i j =>
    ∑ᶠ y : ℤ, t^(((k:ℤ)+1)*y^2-paperIndex j*y)*
      lambdaKernel (classicalCoefficients x) i (paperIndex j-(2*(k:ℤ)+2)*y)
  have hζ : zetaSign F n k≠0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hpair : ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bC0Seq t)).det=omegaSign F k*A.det := by
    have hm : (DC (k := k) (classicalCoefficients x)).transpose*
        CC (n := n) (k := k) (bC0Seq t) =
      Matrix.of fun i j => (-1:F)^(j.val+1)*A i j := by
      ext i j
      exact DC_CC_C0_pairing x t i j
    rw [hm,← prod_first_sign]
    exact det_mul_row _ A
  rw [prop_2_2_C0 x t hn hk hDelta]
  have htr := normalized_transfer_3_1 (PhiC (k := k) x) (VC0 t)
    (DC (k := k) (classicalCoefficients x)) (CC (n := n) (k := k) (bC0Seq t))
    (lemma_3_2_PhiC_DC x) (VC0_transpose_CC t ht hk) hDelta
    (by rw [lemma_3_2_minor_DC]; exact hζ) (prop_2_2_minor_VC0 t hk)
    (by rw [CC_C0_head,det_one]; exact one_ne_zero)
  rw [lemma_3_2_minor_DC,CC_C0_head,det_one,hpair] at htr
  change (PhiC (k := k) x*VC0 t).det/DeltaC x=_ at htr
  have he : (PhiC (k := k) x*VC0 t).det/DeltaC x=A.det := by
    rw [htr]
    unfold zetaSign
    have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
    field_simp
  refine he.trans ?_
  exact det_finsum_eq_JK (2*(k:ℤ)+2) (by omega) _ _
    (lambdaKernel_hasFiniteSupport _)

/-- At zero parameter every nonzero affine shift has zero weight. -/
theorem C0_weight_zero (j : Fin k) (y : ℤ) (hy : y≠0) :
    (0:F)^(((k:ℤ)+1)*y^2-paperIndex j*y)=0 := by
  have hk : 0 < k := by have hj := j.isLt; omega
  exact _root_.zero_zpow _ (ne_of_gt (C0_exponent_pos hk j y hy))

/-- The zero endpoint is the specialization of the nonzero-parameter affine
identity, after both sides have been lifted to parameter polynomials. -/
theorem ordinary_C0_zero [CharZero F] (x : Fin n → Fˣ)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedC0 x 0 k=JK (k := k) (2*(k:ℤ)+2)
      (fun j y => (0:F)^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  classical
  let E (j : Fin k) (y : ℤ) : ℤ := ((k : ℤ)+1)*y^2-paperIndex j*y
  have hpow (t : F) (j : Fin k) (y : ℤ) : t^(E j y).toNat = t^(E j y) :=
    pow_toNat_eq_zpow t _ (C0_exponent_nonneg j y)
  have h := reducedWeyl_eq_JK_zero_of_nonzero x (2*(k:ℤ)+2) (by omega)
    1 (by omega) (fun z => (1-z^2)⁻¹) (fun _ => 0)
    (fun j y => (E j y).toNat) (fun _ _ => (1:F))
    (lambdaKernel (classicalCoefficients x)) (lambdaKernel_hasFiniteSupport _) (1:F)
    (by
      intro t ht
      have ha := ordinary_C0_nonzero x t ht hn hk hDelta
      simpa only [RedC0, pow_one, mul_zero, add_zero, one_mul, hpow, E] using ha)
  simpa only [RedC0, one_mul, hpow, E] using h

/-- Proposition 4.1 / equation (1.6), including zero parameter. -/
theorem ordinary_C0_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedC0 x t k=JK (k := k) (2*(k:ℤ)+2)
      (fun j y => t^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  by_cases ht : t=0
  · subst t
    exact ordinary_C0_zero x hn hk hDelta
  · exact ordinary_C0_nonzero x t ht hn hk hDelta

end
end AffineDualJT
