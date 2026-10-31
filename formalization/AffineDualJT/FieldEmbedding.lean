import AffineDualJT.ParameterPolynomials

/-! Transport of the finite Weyl and coefficient expressions along a field
embedding. This permits the polynomial specialization argument to descend
from an infinite extension without changing the original field hypotheses. -/

namespace AffineDualJT
open scoped BigOperators
open Matrix Polynomial AffineDetSum
noncomputable section

variable {F G : Type*} [Field F] [Field G]

def mapWeylVariables {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) : Fin n → Gˣ :=
  fun a => Units.map φ.toMonoidHom (x a)

theorem map_dotE {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) :
    (dotE x).map φ = dotE (mapWeylVariables φ x) := by
  simp [dotE, reciprocalFactor, mapWeylVariables, Polynomial.map_prod,
    Polynomial.map_mul, Units.coe_map]

theorem map_intCoeff (φ : F →+* G) (P : Polynomial F) (r : ℤ) :
    φ (intCoeff P r) = intCoeff (P.map φ) r := by
  by_cases hr : r < 0 <;> simp [intCoeff, hr, Polynomial.coeff_map]

theorem map_classical_eDot {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) (r : ℤ) :
    φ ((classicalCoefficients x).eDot r) =
      (classicalCoefficients (mapWeylVariables φ x)).eDot r := by
  change φ (intCoeff (dotE x) r) = intCoeff (dotE (mapWeylVariables φ x)) r
  rw [map_intCoeff, map_dotE]

theorem map_lambdaKernel {n k : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    φ (lambdaKernel (classicalCoefficients x) i m) =
      lambdaKernel (classicalCoefficients (mapWeylVariables φ x)) i m := by
  simp only [lambdaKernel, map_sub, map_classical_eDot]

theorem map_hKernel {n k : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    φ (hKernel (classicalCoefficients x) i m) =
      hKernel (classicalCoefficients (mapWeylVariables φ x)) i m := by
  simp only [hKernel, map_add, map_classical_eDot]

theorem map_DeltaC {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) :
    φ (DeltaC x) = DeltaC (mapWeylVariables φ x) := by
  unfold DeltaC
  rw [φ.map_det (fun a r => phi (paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F)]
  apply congrArg Matrix.det
  ext a r
  change φ (phi (paperIndex r) (x a : F)) = phi (paperIndex r) (mapWeylVariables φ x a : G)
  simp only [phi, map_sub, map_zpow₀, mapWeylVariables, Units.coe_map]
  rfl

theorem map_DeltaB {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ) :
    φ (DeltaB x) = DeltaB (mapWeylVariables φ x) := by
  unfold DeltaB
  rw [φ.map_det (fun a r => psi (paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F)]
  apply congrArg Matrix.det
  ext a r
  change φ (psi (paperIndex r) (x a : F)) = psi (paperIndex r) (mapWeylVariables φ x a : G)
  simp only [psi, map_sub, map_zpow₀, mapWeylVariables, Units.coe_map]
  rfl

theorem map_reducedWeyl {n : ℕ} (φ : F →+* G) (x : Fin n → Fˣ)
    (t : F) (k : ℕ) (rho : F → F) (rho' : G → G)
    (hrho : ∀ z, φ (rho z) = rho' (φ z)) :
    φ (reducedWeyl x t k rho) =
      reducedWeyl (mapWeylVariables φ x) (φ t) k rho' := by
  classical
  have hv (η : Fin n → Bool) (a : Fin n) :
      φ (if η a = true then (x a : F)⁻¹ else (x a : F)) =
        if η a = true then (mapWeylVariables φ x a : G)⁻¹ else (mapWeylVariables φ x a : G) := by
    split <;> simp [mapWeylVariables, map_inv₀]
  simp only [reducedWeyl, div_eq_mul_inv, map_sum, map_prod, map_mul, map_pow,
    map_sub, map_one, map_inv₀, hrho, hv]

theorem map_JK {k : ℕ} (φ : F →+* G) (K : ℤ) (hK : K ≠ 0)
    (w f : Fin k → ℤ → F) (hf : ∀ i, Function.HasFiniteSupport (f i)) :
    φ (JK K w f) = JK K (fun j y => φ (w j y)) (fun i m => φ (f i m)) := by
  classical
  have hs := jkMatrix_det_hasFiniteSupport K hK w f hf
  unfold JK
  rw [map_finsum φ hs]
  apply finsum_congr
  intro y
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change φ (w j (y i) * f i (paperIndex j-K*y i)) = _
  simp [jkMatrix]

end
end AffineDualJT
