import Mathlib

/-!
# The coefficient polynomials, source.tex (1.1)

`dotE` and `ddotE` are the actual finite products from the paper. Integer coefficients use zero extension. Palindromicity is proved by reflecting each quadratic factor and then their product; it is not assumed of the concrete data.
-/

namespace AffineDualJT
open scoped BigOperators Polynomial
noncomputable section

/-- The coefficient properties used by the row kernels. -/
structure CoeffSystem (R : Type*) [CommRing R] (n : ℕ) where
  eDot : ℤ → R
  eDdot : ℤ → R
  eDot_zero_of_neg : ∀ r : ℤ, r < 0 → eDot r = 0
  eDot_zero_of_gt : ∀ r : ℤ, 2 * (n : ℤ) < r → eDot r = 0
  eDdot_zero_of_neg : ∀ r : ℤ, r < 0 → eDdot r = 0
  eDdot_zero_of_gt : ∀ r : ℤ, 2 * (n : ℤ) + 1 < r → eDdot r = 0
  eDot_pal : ∀ r : ℤ, eDot (2 * (n : ℤ) - r) = eDot r
  eDdot_pal : ∀ r : ℤ, eDdot (2 * (n : ℤ) + 1 - r) = eDdot r
  eDdot_eq : ∀ r : ℤ, eDdot r = eDot r + eDot (r - 1)

namespace CoeffSystem
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Zero extension in (1.1) gives actual finite support, including negative indices. -/
theorem eDot_hasFiniteSupport (c : CoeffSystem R n) : Function.HasFiniteSupport c.eDot := by
  refine (Set.finite_Icc (0 : ℤ) (2 * (n : ℤ))).subset ?_
  intro r hr
  have hne : c.eDot r ≠ 0 := hr
  constructor
  · by_contra hlo
    exact hne (c.eDot_zero_of_neg r (by omega))
  · by_contra hhi
    exact hne (c.eDot_zero_of_gt r (by omega))

theorem eDdot_hasFiniteSupport (c : CoeffSystem R n) : Function.HasFiniteSupport c.eDdot := by
  refine (Set.finite_Icc (0 : ℤ) (2 * (n : ℤ) + 1)).subset ?_
  intro r hr
  have hne : c.eDdot r ≠ 0 := hr
  constructor
  · by_contra hlo
    exact hne (c.eDdot_zero_of_neg r (by omega))
  · by_contra hhi
    exact hne (c.eDdot_zero_of_gt r (by omega))

end CoeffSystem

section PolynomialCoefficients
variable {R : Type*} [CommRing R]

/-- Coefficients at all integer indices, extended by zero below zero. -/
def intCoeff (P : R[X]) (r : ℤ) : R :=
  if r < 0 then 0 else P.coeff r.toNat

@[simp] theorem intCoeff_of_neg (P : R[X]) {r : ℤ} (hr : r < 0) :
    intCoeff P r = 0 := by simp [intCoeff, hr]

theorem intCoeff_of_nonneg (P : R[X]) {r : ℤ} (hr : 0 ≤ r) :
    intCoeff P r = P.coeff r.toNat := by simp [intCoeff, not_lt.mpr hr]

@[simp] theorem intCoeff_nat (P : R[X]) (r : ℕ) :
    intCoeff P r = P.coeff r := by simp [intCoeff]

theorem intCoeff_zero_of_gt (P : R[X]) (N : ℕ) (hP : P.natDegree ≤ N)
    (r : ℤ) (hr : (N : ℤ) < r) : intCoeff P r = 0 := by
  rw [intCoeff_of_nonneg P (by omega)]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have : N < r.toNat := by omega
  omega

/-- Reflection of a bounded polynomial gives the paper's integer-index symmetry. -/
theorem intCoeff_pal (P : R[X]) (N : ℕ) (hP : P.natDegree ≤ N)
    (hpal : P.reflect N = P) (r : ℤ) :
    intCoeff P ((N : ℤ) - r) = intCoeff P r := by
  by_cases hr : r < 0
  · rw [intCoeff_of_neg P hr, intCoeff_zero_of_gt P N hP _ (by omega)]
  by_cases hNr : (N : ℤ) < r
  · rw [intCoeff_zero_of_gt P N hP r hNr, intCoeff_of_neg P (by omega)]
  have hr0 : 0 ≤ r := by omega
  rw [intCoeff_of_nonneg P (by omega), intCoeff_of_nonneg P hr0]
  have hnat : ((N : ℤ) - r).toNat = N - r.toNat := by omega
  rw [hnat]
  have h := congrArg (fun Q : R[X] => Q.coeff r.toNat) hpal
  simpa only [Polynomial.coeff_reflect, Polynomial.revAt_le (show r.toNat ≤ N by omega)]
    using h

/-- Multiplication by `1+u` is the adjacent-coefficient relation of (1.1). -/
theorem intCoeff_one_add_X_mul (P : R[X]) (r : ℤ) :
    intCoeff ((1 + Polynomial.X) * P) r = intCoeff P r + intCoeff P (r - 1) := by
  by_cases hr : r < 0
  · simp [intCoeff_of_neg _ hr, intCoeff_of_neg P (show r - 1 < 0 by omega)]
  have hr0 : 0 ≤ r := by omega
  rw [intCoeff_of_nonneg _ hr0, intCoeff_of_nonneg P hr0, add_mul, one_mul,
    Polynomial.coeff_add]
  by_cases hz : r = 0
  · subst r
    simp [intCoeff]
  have hpos : 0 ≤ r - 1 := by omega
  rw [intCoeff_of_nonneg P hpos]
  have hs : r.toNat = (r - 1).toNat + 1 := by omega
  rw [hs, Polynomial.coeff_X_mul]

end PolynomialCoefficients

section Classical
variable {F : Type*} [Field F]

/-- One reciprocal pair in `dotE(u)`. -/
def reciprocalFactor (x : Fˣ) : F[X] :=
  (1 + Polynomial.C (x : F) * Polynomial.X) *
    (1 + Polynomial.C (↑(x⁻¹) : F) * Polynomial.X)

theorem reciprocalFactor_eq (x : Fˣ) :
    reciprocalFactor x =
      1 + Polynomial.C ((x : F) + ↑(x⁻¹)) * Polynomial.X + Polynomial.X ^ 2 := by
  have hx : (x : F) * (↑(x⁻¹) : F) = 1 := by simp
  unfold reciprocalFactor
  rw [map_add]
  have hC : Polynomial.C (x : F) * Polynomial.C (↑(x⁻¹) : F) = (1 : F[X]) := by
    rw [← map_mul, hx, map_one]
  calc
    _ = 1 + (Polynomial.C (x : F) + Polynomial.C (↑(x⁻¹) : F)) * Polynomial.X +
        (Polynomial.C (x : F) * Polynomial.C (↑(x⁻¹) : F)) * Polynomial.X ^ 2 := by ring
    _ = _ := by rw [hC, one_mul]

theorem reciprocalFactor_degree_le (x : Fˣ) : (reciprocalFactor x).natDegree ≤ 2 := by
  rw [reciprocalFactor_eq]
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  · simp

theorem reciprocalFactor_reflect (x : Fˣ) :
    (reciprocalFactor x).reflect 2 = reciprocalFactor x := by
  rw [reciprocalFactor_eq]
  have hmid (a : F) : (Polynomial.C a * Polynomial.X).reflect 2 =
      Polynomial.C a * Polynomial.X := by
    simpa using Polynomial.reflect_C_mul_X_pow (R := F) 2 1 (c := a)
  rw [Polynomial.reflect_add, Polynomial.reflect_add, Polynomial.reflect_one, hmid]
  simp [Polynomial.reflect_monomial, add_comm, add_left_comm]

private theorem reciprocalProduct_properties {ι : Type*} (s : Finset ι) (x : ι → Fˣ) :
    (∏ a ∈ s, reciprocalFactor (x a)).natDegree ≤ 2 * s.card ∧
      (∏ a ∈ s, reciprocalFactor (x a)).reflect (2 * s.card) =
        ∏ a ∈ s, reciprocalFactor (x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hN : 2 * (s.card + 1) = 2 + 2 * s.card := by omega
    rw [hN]
    constructor
    · exact Polynomial.natDegree_mul_le.trans
        (Nat.add_le_add (reciprocalFactor_degree_le _) ih.1)
    · rw [Polynomial.reflect_mul _ _ (reciprocalFactor_degree_le _) ih.1,
        reciprocalFactor_reflect, ih.2]

/-- `dotE(u)=∏ₐ(1+uxₐ)(1+uxₐ⁻¹)`, source.tex (1.1). -/
def dotE {n : ℕ} (x : Fin n → Fˣ) : F[X] := ∏ a, reciprocalFactor (x a)

/-- `ddotE(u)=(1+u)dotE(u)`, source.tex (1.1). -/
def ddotE {n : ℕ} (x : Fin n → Fˣ) : F[X] := (1 + Polynomial.X) * dotE x

theorem dotE_degree_le {n : ℕ} (x : Fin n → Fˣ) : (dotE x).natDegree ≤ 2 * n := by
  simpa [dotE] using (reciprocalProduct_properties Finset.univ x).1

theorem dotE_reflect {n : ℕ} (x : Fin n → Fˣ) : (dotE x).reflect (2 * n) = dotE x := by
  simpa [dotE] using (reciprocalProduct_properties Finset.univ x).2

theorem ddotE_degree_le {n : ℕ} (x : Fin n → Fˣ) : (ddotE x).natDegree ≤ 2 * n + 1 := by
  have h : (1 + Polynomial.X : F[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le <;> simp
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add h (dotE_degree_le x)).trans (by omega))

theorem ddotE_reflect {n : ℕ} (x : Fin n → Fˣ) :
    (ddotE x).reflect (2 * n + 1) = ddotE x := by
  have h : (1 + Polynomial.X : F[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le <;> simp
  unfold ddotE
  rw [show 2 * n + 1 = 1 + 2 * n by omega,
    Polynomial.reflect_mul _ _ h (dotE_degree_le x), dotE_reflect]
  simp [Polynomial.reflect_add, add_comm]

/-- The concrete coefficient system of (1.1), with every property proved. -/
def classicalCoefficients {n : ℕ} (x : Fin n → Fˣ) : CoeffSystem F n where
  eDot := intCoeff (dotE x)
  eDdot := intCoeff (ddotE x)
  eDot_zero_of_neg := fun _ hr => intCoeff_of_neg _ hr
  eDot_zero_of_gt := by
    intro r hr
    exact intCoeff_zero_of_gt _ (2 * n) (dotE_degree_le x) r (by exact_mod_cast hr)
  eDdot_zero_of_neg := fun _ hr => intCoeff_of_neg _ hr
  eDdot_zero_of_gt := by
    intro r hr
    exact intCoeff_zero_of_gt _ (2 * n + 1) (ddotE_degree_le x) r (by exact_mod_cast hr)
  eDot_pal := by
    intro r
    simpa using intCoeff_pal _ (2 * n) (dotE_degree_le x) (dotE_reflect x) r
  eDdot_pal := by
    intro r
    simpa using intCoeff_pal _ (2 * n + 1) (ddotE_degree_le x) (ddotE_reflect x) r
  eDdot_eq := intCoeff_one_add_X_mul (dotE x)

@[simp] theorem classicalCoefficients_eDot_zero {n : ℕ} (x : Fin n → Fˣ) :
    (classicalCoefficients x).eDot 0 = 1 := by
  change intCoeff (dotE x) 0 = 1
  rw [intCoeff_of_nonneg _ (by omega)]
  simp [dotE, Polynomial.coeff_zero_prod, reciprocalFactor,
    Polynomial.mul_coeff_zero]

end Classical
end
end AffineDualJT
