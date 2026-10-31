import AffineDualJT.OrdinaryC0Identity
import AffineDualJT.OrdinaryBCIdentity
import AffineDualJT.OrdinaryBIdentities

/-! # Propositions 4.1 and 4.2, the four ordinary affine identities -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
open AffineDetSum
noncomputable section
section Props
variable {F : Type*} [Field F]

/-- Proposition 4.1 / equation (1.6), positive width. -/
theorem prop_4_1_C0 [CharZero F] {n k : ℕ} (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedC0 x t k = JK (k := k) (2*(k:ℤ)+2)
      (fun j y => t^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  exact ordinary_C0_identity x t hn hk hDelta

/-- Proposition 4.1 / equation (1.8), positive width. -/
theorem prop_4_1_BC [CharZero F] {n k : ℕ} (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedBC x τ k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y * τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  exact ordinary_BC_identity x τ hn hk hDelta

/-- Proposition 4.2 / equation (1.3), positive width. -/
theorem prop_4_2_B0 [CharZero F] {n k : ℕ} (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedB0 x t k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y *
        t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  exact ordinary_B0_identity x t hn hk hDelta

/-- Proposition 4.2 / equation (1.4), positive width. -/
theorem prop_4_2_Bminus [CharZero F] {n k : ℕ} (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedBminus x τ k = JK (k := k) (2*(k:ℤ))
      (fun j y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  exact ordinary_Bminus_identity x τ hn hk hDelta

end Props
end
end AffineDualJT
