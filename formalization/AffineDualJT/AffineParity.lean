import AffineDualJT.DeterminantFinsum

/-! # The even-sublattice projector in Proposition 5.1 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] {k : ℕ}

theorem neg_one_zpow_sum (y : Fin k → ℤ) :
    (∏ i : Fin k, (-1:F)^(y i))=(-1:F)^(∑ i : Fin k, y i) := by
  have h (s : Finset (Fin k)) : (∏ i ∈ s, (-1:F)^(y i))=(-1:F)^(∑ i ∈ s, y i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,zpow_add₀ (by norm_num : (-1:F)≠0)]
  exact h Finset.univ

theorem jkMatrix_signed_det (K : ℤ) (w f : Fin k → ℤ → F) (y : Fin k → ℤ) :
    (jkMatrix K (fun j m => (-1:F)^m*w j m) f y).det=
      (-1:F)^(∑ i : Fin k, y i)*(jkMatrix K w f y).det := by
  have hm : jkMatrix K (fun j m => (-1:F)^m*w j m) f y=
      Matrix.of fun i j => (-1:F)^(y i)*jkMatrix K w f y i j := by
    ext i j
    simp only [jkMatrix,Matrix.of_apply,mul_assoc]
  rw [hm,det_mul_column,neg_one_zpow_sum]

/-- The finite support justifies the parity projector and both determinant sums. -/
theorem JKEven_projector [CharZero F] (K : ℤ) (hK : K≠0)
    (w f : Fin k → ℤ → F) (hf : ∀ i, Function.HasFiniteSupport (f i)) :
    JKEven K w f=(2:F)⁻¹*(JK K w f+JK K (fun j m => (-1:F)^m*w j m) f) := by
  classical
  have hd := jkMatrix_det_hasFiniteSupport K hK w f hf
  have hs : Function.HasFiniteSupport (fun y : Fin k → ℤ =>
      (-1:F)^(∑ i : Fin k, y i)*(jkMatrix K w f y).det) :=
    Function.HasFiniteSupport.mul_right _ hd
  have hp (y : Fin k → ℤ) :
      (if EvenVector y then (jkMatrix K w f y).det else 0)=
        (2:F)⁻¹*((jkMatrix K w f y).det+
          (-1:F)^(∑ i : Fin k, y i)*(jkMatrix K w f y).det) := by
    unfold EvenVector
    by_cases he : Even (∑ i : Fin k, y i)
    · rw [ite_eq_left he,he.neg_one_zpow,one_mul]
      field_simp
      ring
    · rw [ite_eq_right he,(Int.not_even_iff_odd.mp he).neg_one_zpow]
      ring
  unfold JKEven
  simp only [finsum_eq_if,hp]
  rw [← mul_finsum,finsum_add_distrib hd hs]
  unfold JK
  rw [show (∑ᶠ y : Fin k → ℤ, (jkMatrix K (fun j m => (-1:F)^m*w j m) f y).det)=
    ∑ᶠ y : Fin k → ℤ, (-1:F)^(∑ i : Fin k, y i)*(jkMatrix K w f y).det by
      exact finsum_congr (jkMatrix_signed_det K w f)]

end
end AffineDualJT
