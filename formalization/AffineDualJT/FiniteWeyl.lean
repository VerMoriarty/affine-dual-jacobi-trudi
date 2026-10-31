import AffineDualJT.AlternantFactorization
import AffineDualJT.AlternantPaperRoute
import AffineDualJT.PaperAlternantDivisibility
import AffineDualJT.PaperAlternantNormalization

/-!
# Finite Weyl alternants (§2.1)

Lemma 2.1, equations (2.3)--(2.5). The three polynomial alternant
factorizations are established in the polynomial ring by the paper's factor
divisibility, exact degree comparison, and lowest-homogeneous-part
normalization. The resulting identities are then evaluated at arbitrary
nodes, including zero variables. The matrices and Weyl denominator products
from (2.6) are defined and proved in `WeylMatrices` and `WeylDenominators`.
-/

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

/-- Lemma 2.1, equation (2.3), p.4. -/
theorem lemma_2_1_eq_2_3 {n : ℕ} (t : F) (z : Fin n → F) :
    Matrix.det (fun a r => fColumn t r (z a) : Matrix (Fin n) (Fin n) F) = Nt t z := by
  classical
  have hp : paperBasicAlternantPolynomial (n := n) t =
      paperBasicFactorProduct (n := n) t := by
    by_cases ht : t = 0
    · subst t
      exact paper_basic_factorization_zero
    · exact paper_basic_factorization_by_lowest_part t ht
  rw [paper_basic_factor_product_eq_Nt] at hp
  have he := congrArg (MvPolynomial.eval z) hp
  simp only [paperBasicAlternantPolynomial, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map, Matrix.of_apply, map_fColumn, map_Nt,
    MvPolynomial.eval_C, MvPolynomial.eval_X] at he
  convert he using 1
  rfl

/-- Lemma 2.1, equation (2.4), p.4. -/
theorem lemma_2_1_eq_2_4 {n : ℕ} (t : F) (z : Fin n → F) :
    Matrix.det (fun a r =>
      z a ^ (n - (r.1 + 1)) - t ^ (r.1 + 1) * z a ^ (n + r.1 + 1) :
      Matrix (Fin n) (Fin n) F) =
      (∏ a : Fin n, (1 - t * z a ^ 2)) * Nt t z := by
  classical
  have hp : paperCtAlternantPolynomial (n := n) t =
      paperCtFactorProduct (n := n) t := by
    by_cases ht : t = 0
    · subst t
      exact paper_ct_factorization_zero
    · exact paper_ct_factorization_by_lowest_part t ht
  rw [paper_ct_factor_product_eq] at hp
  have he := congrArg (MvPolynomial.eval z) hp
  simp only [paperCtAlternantPolynomial, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map, Matrix.of_apply, map_ctAlternantColumn, map_Nt, map_mul, map_prod,
    map_sub, map_one, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X] at he
  convert he using 1
  rfl

/-- Lemma 2.1, equation (2.5), p.4; here `t=τ²`. -/
theorem lemma_2_1_eq_2_5 {n : ℕ} (τ : F) (z : Fin n → F) :
    Matrix.det (fun a r =>
      z a ^ (n - (r.1 + 1)) + τ ^ (2 * r.1 + 1) * z a ^ (n + r.1) :
      Matrix (Fin n) (Fin n) F) =
      (∏ a : Fin n, (1 + τ * z a)) * Nt (τ ^ 2) z := by
  classical
  have hp : paperBminusAlternantPolynomial (n := n) τ =
      paperBminusFactorProduct (n := n) τ := by
    by_cases hτ : τ = 0
    · subst τ
      exact paper_bminus_factorization_zero
    · exact paper_bminus_factorization_by_lowest_part τ hτ
  rw [paper_bminus_factor_product_eq] at hp
  have he := congrArg (MvPolynomial.eval z) hp
  simp only [paperBminusAlternantPolynomial, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map, Matrix.of_apply, map_bminusAlternantColumn, map_Nt, map_mul, map_prod,
    map_add, map_one, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X] at he
  convert he using 1
  rfl

/-- Matrix-constructor form of (2.3), for finite-folding applications. -/
theorem lemma_2_1_eq_2_3_of {n : ℕ} (t : F) (z : Fin n → F) :
    (Matrix.of fun a r : Fin n => fColumn t r (z a)).det = Nt t z := by
  have hm : (Matrix.of fun a r : Fin n => fColumn t r (z a)) =
      (fun a r => fColumn t r (z a) : Matrix (Fin n) (Fin n) F) := by
    ext a r
    rfl
  rw [hm]
  exact lemma_2_1_eq_2_3 t z

/-- Matrix-constructor form of (2.4), for finite-folding applications. -/
theorem lemma_2_1_eq_2_4_of {n : ℕ} (t : F) (z : Fin n → F) :
    (Matrix.of fun a r : Fin n => ctAlternantColumn t r (z a)).det =
      (∏ a : Fin n, (1-t*z a^2))*Nt t z := by
  have hm : (Matrix.of fun a r : Fin n => ctAlternantColumn t r (z a)) =
      (fun a r => ctAlternantColumn t r (z a) : Matrix (Fin n) (Fin n) F) := by
    ext a r
    rfl
  rw [hm]
  simpa only [ctAlternantColumn] using lemma_2_1_eq_2_4 t z

/-- Matrix-constructor form of (2.5), for finite-folding applications. -/
theorem lemma_2_1_eq_2_5_of {n : ℕ} (τ : F) (z : Fin n → F) :
    (Matrix.of fun a r : Fin n => bminusAlternantColumn τ r (z a)).det =
      (∏ a : Fin n, (1+τ*z a))*Nt (τ^2) z := by
  have hm : (Matrix.of fun a r : Fin n => bminusAlternantColumn τ r (z a)) =
      (fun a r => bminusAlternantColumn τ r (z a) : Matrix (Fin n) (Fin n) F) := by
    ext a r
    rfl
  rw [hm]
  simpa only [bminusAlternantColumn] using lemma_2_1_eq_2_5 τ z

end
end AffineDualJT
