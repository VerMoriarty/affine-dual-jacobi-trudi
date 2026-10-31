import AffineDualJT.Basic

/-!
# The rectangular Weyl sum, source.tex (2.1)

The finite signed permutation orbit and both normalization factors are
explicit. The definitions in `ExternalHallLittlewood` use this Weyl sum,
not the desired affine determinant or the reduced sign sum.

`Admissible` describes a common sufficient regularity domain for evaluating
these rational expressions in a general field. The paper uses algebraically
independent variables, for which these denominator conditions hold. The
raw expression uses Lean's totalized field division, so its value at a
singular input is not automatically the value of a cancelled polynomial.
The `Admissible` hypotheses on the raw interfaces are retained.
-/
open scoped BigOperators
namespace AffineDualJT
noncomputable section
namespace ExternalHL
variable {F : Type*} [Field F]
def Vn (n : ℕ) (t : F) : F :=
  ∏ r : Fin n, ∑ l ∈ Finset.range (r.val+1), t^l

def pochhammer (n : ℕ) (a t : F) : F :=
  ∏ r : Fin n, (1-a*t^r.val)

def signedVariables {n : ℕ} (x : Fin n → Fˣ) (η : Fin n → Bool) (a : Fin n) : F :=
  if η a = true then (x a : F)⁻¹ else (x a : F)

def weylVariables {n : ℕ} (x : Fin n → Fˣ) (σ : Equiv.Perm (Fin n))
    (η : Fin n → Bool) (a : Fin n) : F :=
  signedVariables x η (σ a)

def weylSummand {n : ℕ} (t : F) (k : ℕ) (rho : F → F) (u : Fin n → F) : F :=
  (∏ a : Fin n, (u a)⁻¹^k * rho (u a)) *
    (∏ a : Fin n, ∏ b : {b : Fin n // a < b.val},
      ((t*u a-u b.val)*(1-t*u a*u b.val))/((u a-u b.val)*(1-u a*u b.val)))

def weylSum {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) (rho : F → F) (ν : F) : F :=
  (∑ σ : Equiv.Perm (Fin n), ∑ η : Fin n → Bool,
    weylSummand t k rho (weylVariables x σ η)) / (Vn n t * ν)

def nuCt (n k : ℕ) (t : F) : F := if k=0 then pochhammer n (-t) t else 1

def nuBminus (n k : ℕ) (τ : F) : F := if k=0 then pochhammer n τ (τ^2) else 1

def nuBplus (n k : ℕ) (t : F) : F := if k=0 then pochhammer n (-1) t else 1
structure Admissible {n : ℕ} (x : Fin n → Fˣ) (t ν : F) : Prop where
  normalization : Vn n t * ν ≠ 0
  distinct : ∀ η : Fin n → Bool, ∀ a b : Fin n, a ≠ b →
    signedVariables x η a - signedVariables x η b ≠ 0
  pair : ∀ η : Fin n → Bool, ∀ a b : Fin n, a ≠ b →
    1-signedVariables x η a*signedVariables x η b ≠ 0
  boundary : ∀ η : Fin n → Bool, ∀ a : Fin n,
    1-(signedVariables x η a)^2 ≠ 0
end ExternalHL
end
end AffineDualJT
