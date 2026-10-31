import AffineDualJT.ExceptionalCtKernels
import AffineDualJT.AffineParity
import AffineDualJT.ClassicalTransfer
import AffineDualJT.WeightExponents

/-! # Proposition 5.1: fixed residues and the even affine sublattice -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem DC_CC_Ct_pairing (x : Fin n → Fˣ) (t : F) (hk : 0<k) (i j : Fin k) :
    ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bCt t)) i j=
      (-1:F)^(j.val+1)*(∑ᶠ y : ℤ,
        ((-1:F)^y*t^((k:ℤ)*y^2-paperIndex j*y))*
          lambdaKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y)) := by
  rw [lemma_3_3_eq_3_5]
  have h := residueSum_pairing (2*(k:ℤ)) (paperIndex j) (by omega)
    (fun m => (-1:F)^m*lambdaKernel (classicalCoefficients x) i m)
    (fun q => (-1:F)^q*t^((k:ℤ)*q^2+paperIndex j*q))
  change (∑ᶠ m : ℤ, ((-1:F)^m*lambdaKernel (classicalCoefficients x) i m)*
    residueSum (2*(k:ℤ)) (paperIndex j)
      (fun q => (-1:F)^q*t^((k:ℤ)*q^2+paperIndex j*q)) m)=_ at ⊢
  rw [h,← finsum_comp_equiv (Equiv.neg ℤ),mul_finsum]
  apply finsum_congr
  intro y
  simp only [Equiv.neg_apply]
  have hs : (-1:F)^(2*(k:ℤ)*(-y))=1 := by
    rw [show 2*(k:ℤ)*(-y)=2*((k:ℤ)*(-y)) by ring]
    exact (even_two_mul _).neg_one_zpow
  have hsy : (-1:F)^(-y)=(-1:F)^y := by
    simp only [← Int.cast_negOnePow F,Int.negOnePow_neg]
  rw [zpow_add₀ (by norm_num : (-1:F)≠0),hs,mul_one,hsy]
  rw [show (k:ℤ)*(-y)^2+paperIndex j*(-y)=(k:ℤ)*y^2-paperIndex j*y by ring,
    show paperIndex j+2*(k:ℤ)*(-y)=paperIndex j-2*(k:ℤ)*y by ring,
    show paperIndex j=((j.val+1:ℕ):ℤ) by simp [paperIndex],zpow_natCast]
  ring

/-- At `t=0`, the Ct exponent is positive for every nonzero shift except
the boundary pair `paperIndex j = k`, `y = 1`. -/
theorem Ct_weight_zero_except (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0)
    (hnot : ¬ (paperIndex j = k ∧ y = 1)) :
    (0:F)^((k:ℤ)*y^2-paperIndex j*y)=0 := by
  apply _root_.zero_zpow
  intro he
  exact hnot ((Ct_exponent_zero_iff hk j y hy).mp he)

/-- The exceptional Ct summand has exponent zero and therefore survives at
`t=0`; it is handled by the parity projection, not entrywise deletion. -/
theorem Ct_weight_exception_one (j : Fin k) (hjk : paperIndex j = k) :
    (0:F)^((k:ℤ)*(1:ℤ)^2-paperIndex j*1)=1 := by
  rw [hjk]
  norm_num

/-- The unsigned last-column summands are exchanged with their negatives. -/
theorem Ct_last_column_sum_zero [CharZero F] (x : Fin n → Fˣ) (t : F)
    (i j : Fin k) (hj : paperIndex j=(k:ℤ)) :
    (∑ᶠ y : ℤ, t^((k:ℤ)*y^2-paperIndex j*y)*
      lambdaKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y))=0 := by
  let a : ℤ → F := fun y => t^((k:ℤ)*y^2-paperIndex j*y)*
    lambdaKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y)
  let e : ℤ ≃ ℤ :=
    { toFun := fun y => 1-y, invFun := fun y => 1-y,
      left_inv := by intro y; dsimp; omega, right_inv := by intro y; dsimp; omega }
  have he (y : ℤ) : a (e y)=-a y := by
    change t^((k:ℤ)*(1-y)^2-paperIndex j*(1-y))*
      lambdaKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*(1-y))=-a y
    rw [show (k:ℤ)*(1-y)^2-paperIndex j*(1-y)=(k:ℤ)*y^2-paperIndex j*y by rw [hj]; ring,
      show paperIndex j-2*(k:ℤ)*(1-y)= -(paperIndex j-2*(k:ℤ)*y) by rw [hj]; ring,
      lambdaKernel_neg,mul_neg]
  have h : (∑ᶠ y : ℤ, a y)= -(∑ᶠ y : ℤ, a y) := by
    calc
      _ = ∑ᶠ y : ℤ, a (e y) := (finsum_comp_equiv e).symm
      _ = ∑ᶠ y : ℤ, -a y := finsum_congr he
      _ = _ := finsum_neg_distrib a
  have htwo : (2:F)*(∑ᶠ y : ℤ, a y)=0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The unsigned full-lattice determinant vanishes, including at zero parameter. -/
theorem Ct_unsigned_JK_zero [CharZero F] (x : Fin n → Fˣ) (t : F) (hk : 0<k) :
    JK (k := k) (2*(k:ℤ)) (fun j y => t^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x))=0 := by
  classical
  rw [← det_finsum_eq_JK (2*(k:ℤ)) (by omega) _ _ (lambdaKernel_hasFiniteSupport _)]
  let j : Fin k := ⟨k-1,by omega⟩
  apply det_eq_zero_of_column_eq_zero j
  intro i
  exact Ct_last_column_sum_zero x t i j (by simp only [j,paperIndex]; omega)

/-- At zero parameter the even-lattice sum is exactly the parity projection
of the signed full-lattice sum; this retains the exceptional Ct shift. -/
theorem Ct_even_sum_zero_parity [CharZero F] (x : Fin n → Fˣ) (hk : 0 < k) :
    JKEven (k := k) (2*(k:ℤ)) (fun j y => (0:F)^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) =
    (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*(0:F)^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  rw [JKEven_projector (2*(k:ℤ)) (by omega) _ _
    (lambdaKernel_hasFiniteSupport _), Ct_unsigned_JK_zero x 0 hk, zero_add]

/-- Complementary transfer gives half of the signed full-lattice determinant. -/
theorem exceptional_Ct_signed_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedCt x t k=(2:F)⁻¹*JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y*t^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  classical
  let A : Matrix (Fin k) (Fin k) F := Matrix.of fun i j =>
    ∑ᶠ y : ℤ, ((-1:F)^y*t^((k:ℤ)*y^2-paperIndex j*y))*
      lambdaKernel (classicalCoefficients x) i (paperIndex j-2*(k:ℤ)*y)
  have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hζ : zetaSign F n k≠0 := mul_ne_zero hs hω
  have hpair : ((DC (k := k) (classicalCoefficients x)).transpose*
      CC (n := n) (k := k) (bCt t)).det=omegaSign F k*A.det := by
    have hm : (DC (k := k) (classicalCoefficients x)).transpose*
        CC (n := n) (k := k) (bCt t)=
      Matrix.of fun i j => (-1:F)^(j.val+1)*A i j := by
      ext i j
      exact DC_CC_Ct_pairing x t hk i j
    rw [hm,← prod_first_sign]
    exact det_mul_row _ A
  rw [prop_2_2_Ct x t hn hk hDelta]
  have htr := normalized_transfer_3_1 (PhiC (k := k) x) (VCt t)
    (DC (k := k) (classicalCoefficients x)) (CC (n := n) (k := k) (bCt t))
    (lemma_3_2_PhiC_DC x) (VCt_transpose_CC_all t hk) hDelta
    (by rw [lemma_3_2_minor_DC]; exact hζ) (prop_2_2_minor_VCt t hk)
    (by rw [CC_Ct_head t hk]; norm_num)
  rw [lemma_3_2_minor_DC,CC_Ct_head t hk,hpair] at htr
  change (PhiC (k := k) x*VCt t : Matrix (Fin n) (Fin n) F).det/DeltaC x=_ at htr
  have he : (PhiC (k := k) x*VCt t : Matrix (Fin n) (Fin n) F).det/DeltaC x=(2:F)⁻¹*A.det := by
    refine htr.trans ?_
    unfold zetaSign
    field_simp
  refine he.trans ?_
  exact congrArg (fun z : F => (2:F)⁻¹*z)
    (det_finsum_eq_JK (2*(k:ℤ)) (by omega) _ _ (lambdaKernel_hasFiniteSupport _))

/-- Equation (1.7), with the even sublattice retained exactly as in the paper. -/
theorem exceptional_Ct_identity [CharZero F] (x : Fin n → Fˣ) (t : F)
    (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x≠0) :
    RedCt x t k=JKEven (k := k) (2*(k:ℤ))
      (fun j y => t^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) := by
  rw [JKEven_projector _ (by omega) _ _ (lambdaKernel_hasFiniteSupport _),
    Ct_unsigned_JK_zero x t hk,zero_add]
  exact exceptional_Ct_signed_identity x t hn hk hDelta

end
end AffineDualJT
