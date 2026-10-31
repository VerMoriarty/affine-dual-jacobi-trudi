import AffineDualJT.FiniteColumnData
import AffineDualJT.DeterminantFinsum
import Mathlib.Algebra.Polynomial.Roots

/-! Polynomial representatives in the deformation parameter.  The fixed
Weyl denominators are coefficients in the base field; no evaluation map from
a rational function field at zero is used. -/

namespace AffineDualJT
open scoped BigOperators
open Matrix Polynomial AffineDetSum
noncomputable section

variable {F : Type*} [Field F]

theorem pow_toNat_eq_zpow (t : F) (e : ℤ) (he : 0 ≤ e) :
    t ^ e.toNat = t ^ e := by
  rw [← zpow_natCast, Int.toNat_of_nonneg he]

/-- A polynomial in the deformation parameter representing the reduced Weyl
sum. The polynomial `q` represents its pair parameter and `rho` represents
the one-variable factor. -/
def parameterWeylPolynomial {n : ℕ} (x : Fin n → Fˣ) (k : ℕ)
    (q : Polynomial F) (rho : F → Polynomial F) : Polynomial F :=
  ∑ η : Fin n → Bool,
    (∏ a : Fin n,
      Polynomial.C (((if η a = true then (x a : F)⁻¹ else (x a : F))⁻¹) ^ k) *
        rho (if η a = true then (x a : F)⁻¹ else (x a : F))) *
    (∏ a : Fin n, ∏ b : {b : Fin n // a < b.1},
      (1 - q * Polynomial.C (if η a = true then (x a : F)⁻¹ else (x a : F)) *
        Polynomial.C (if η b.1 = true then (x b.1 : F)⁻¹ else (x b.1 : F))) *
      Polynomial.C ((1 - (if η a = true then (x a : F)⁻¹ else (x a : F)) *
        (if η b.1 = true then (x b.1 : F)⁻¹ else (x b.1 : F)))⁻¹))

theorem eval_parameterWeylPolynomial {n : ℕ} (x : Fin n → Fˣ) (k : ℕ)
    (q : Polynomial F) (rho : F → Polynomial F) (t : F) :
    Polynomial.eval t (parameterWeylPolynomial x k q rho) =
      reducedWeyl x (Polynomial.eval t q) k (fun z => Polynomial.eval t (rho z)) := by
  classical
  have hC (a : F) : (Polynomial.evalRingHom t) (Polynomial.C a) = a := by simp
  change (Polynomial.evalRingHom t) (parameterWeylPolynomial x k q rho) = _
  simp only [parameterWeylPolynomial, reducedWeyl, map_sum, map_prod, map_mul,
    map_sub, map_one, hC, div_eq_mul_inv]
  rfl

/-- The polynomial affine sum uses the same determinant summands as (1.2),
with nonnegative natural exponents and parameter-free coefficients. -/
def parameterJKPolynomial {k : ℕ} (K : ℤ) (e : Fin k → ℤ → ℕ)
    (c f : Fin k → ℤ → F) : Polynomial F :=
  JK K (fun j y => Polynomial.C (c j y) * Polynomial.X ^ e j y)
    (fun i m => Polynomial.C (f i m))

theorem eval_parameterJKPolynomial {k : ℕ} (K : ℤ) (hK : K ≠ 0)
    (e : Fin k → ℤ → ℕ) (c f : Fin k → ℤ → F)
    (hf : ∀ i, Function.HasFiniteSupport (f i)) (t : F) :
    Polynomial.eval t (parameterJKPolynomial K e c f) =
      JK K (fun j y => c j y * t ^ e j y) f := by
  classical
  have hfc : ∀ i, Function.HasFiniteSupport (fun m => (Polynomial.C (f i m) : Polynomial F)) := by
    intro i
    exact (hf i).fun_comp (map_zero (Polynomial.C : F →+* Polynomial F))
  let w : Fin k → ℤ → Polynomial F := fun j y => Polynomial.C (c j y) * Polynomial.X ^ e j y
  let g : Fin k → ℤ → Polynomial F := fun i m => Polynomial.C (f i m)
  have hsum := jkMatrix_det_hasFiniteSupport K hK w g hfc
  change (Polynomial.evalRingHom t) (∑ᶠ y : Fin k → ℤ, (jkMatrix K w g y).det) = _
  rw [map_finsum _ hsum]
  unfold JK
  apply finsum_congr
  intro y
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change Polynomial.eval t ((jkMatrix K w g y) i j) = _
  simp [jkMatrix, w, g, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
  ring

/-- An identity between parameter polynomials proved for all nonzero values
also holds at zero over an infinite field. -/
theorem polynomial_eval_zero_of_nonzero [Infinite F] (p q : Polynomial F)
    (h : ∀ t : F, t ≠ 0 → Polynomial.eval t p = Polynomial.eval t q) :
    Polynomial.eval 0 p = Polynomial.eval 0 q := by
  have hinf : Set.Infinite {t : F | t ≠ 0} := by
    have hs : {t : F | t ≠ 0} = ({0} : Set F)ᶜ := by ext t; simp
    rw [hs]
    exact (Set.finite_singleton (0 : F)).infinite_compl
  have hpq : p = q := Polynomial.eq_of_infinite_eval_eq p q
    (hinf.mono (by intro t ht; exact h t ht))
  rw [hpq]

/-- Specialize a reduced Weyl/affine identity by first proving a polynomial
identity in the parameter. The square-root cases use `d = 2` and an affine
one-variable factor; the other cases use `d = 1`. -/
theorem reducedWeyl_eq_JK_zero_of_nonzero [Infinite F] {n k : ℕ}
    (x : Fin n → Fˣ) (K : ℤ) (hK : K ≠ 0) (d : ℕ) (hd : d ≠ 0)
    (a b : F → F) (e : Fin k → ℤ → ℕ) (c f : Fin k → ℤ → F)
    (hf : ∀ i, Function.HasFiniteSupport (f i)) (s : F)
    (h : ∀ t : F, t ≠ 0 →
      reducedWeyl x (t ^ d) k (fun z => a z + t * b z) =
        s * JK K (fun j y => c j y * t ^ e j y) f) :
    reducedWeyl x 0 k a = s * JK K (fun j y => c j y * (0 : F) ^ e j y) f := by
  let P : Polynomial F := parameterWeylPolynomial x k (Polynomial.X ^ d)
    (fun z => Polynomial.C (a z) + Polynomial.X * Polynomial.C (b z))
  let Q : Polynomial F := Polynomial.C s * parameterJKPolynomial K e c f
  have hp (t : F) : Polynomial.eval t P =
      reducedWeyl x (t ^ d) k (fun z => a z + t * b z) := by
    rw [show P = parameterWeylPolynomial x k (Polynomial.X ^ d)
      (fun z => Polynomial.C (a z) + Polynomial.X * Polynomial.C (b z)) by rfl,
      eval_parameterWeylPolynomial]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hq (t : F) : Polynomial.eval t Q =
      s * JK K (fun j y => c j y * t ^ e j y) f := by
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C,
      eval_parameterJKPolynomial K hK e c f hf]
  have he := polynomial_eval_zero_of_nonzero P Q (fun t ht => by rw [hp, hq]; exact h t ht)
  rw [hp, hq] at he
  simpa [zero_pow hd] using he

end
end AffineDualJT
