import AffineDualJT.ClassicalSpecialization
import AffineDualJT.Folding

/-! # Shared determinant transfers and zero-parameter endpoints for §4 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

theorem omegaSign_mul_self : omegaSign F k*omegaSign F k=1 := by
  unfold omegaSign
  rw [← pow_add,← two_mul]
  exact (even_two_mul _).neg_one_pow

/-- The two complementary sign factors cancel in the ordinary B transfer. -/
theorem ordinary_B_transfer (x : Fin n → Fˣ)
    (V : Matrix (Fin (n+k)) (Fin n) F) (b : Fin k → ℤ → F)
    (hVTC : V.transpose*CB (n := n) b=0) (hDelta : DeltaB x≠0)
    (hVH : (lastRowsY V).det=1)
    (hCI : (firstRowsZ (CB (n := n) b)).det=omegaSign F k) :
    (PhiB (k := k) x*V).det/DeltaB x=
      ((DB (k := k) (classicalCoefficients x)).transpose*CB (n := n) b).det := by
  have hs : (-1:F)^(n*k)≠0 := pow_ne_zero _ (by norm_num)
  have hω : omegaSign F k≠0 := pow_ne_zero _ (by norm_num)
  have hζ : zetaSign F n k≠0 := mul_ne_zero hs hω
  have htr := normalized_transfer_3_1 (PhiB (k := k) x) V
    (DB (k := k) (classicalCoefficients x)) (CB (n := n) b)
    (lemma_3_2_PhiB_DB x) hVTC hDelta
    (by rw [lemma_3_2_minor_DB]; exact hζ) hVH (by rw [hCI]; exact hω)
  rw [lemma_3_2_minor_DB,hCI] at htr
  unfold zetaSign at htr
  rw [mul_assoc,omegaSign_mul_self,mul_one,div_self hs,one_mul] at htr
  exact htr

/-- When only the zero shift survives, affine multilinearity is classical. -/
theorem JK_of_zero_shifts (K : ℤ) (hK : K≠0) (w : Fin k → ℤ → F)
    (f : Fin k → ℤ → F) (hf : ∀ i, Function.HasFiniteSupport (f i))
    (hw0 : ∀ j, w j 0=1) (hw : ∀ j y, y≠0 → w j y=0) :
    (Matrix.of fun i j : Fin k => f i (paperIndex j)).det=JK K w f := by
  have hd := det_finsum_eq_JK K hK w f hf
  have hs : (Matrix.of fun i j : Fin k => ∑ᶠ y : ℤ,
      w j y*f i (paperIndex j-K*y)).det=
      (Matrix.of fun i j : Fin k => f i (paperIndex j)).det := by
    apply congrArg Matrix.det
    ext i j
    simp only [Matrix.of_apply]
    rw [finsum_eq_single _ 0]
    · simp only [hw0,mul_zero,sub_zero,one_mul]
    · intro y hy
      rw [hw j y hy,zero_mul]
  exact hs.symm.trans hd

end
end AffineDualJT
