import AffineDualJT.Section4Ordinary
import AffineDualJT.ExceptionalSequences
import AffineDualJT.ExceptionalCtIdentity
import AffineDualJT.ExceptionalBplusIdentity
import AffineDualJT.ExceptionalBtIdentity

/-! # Propositions 5.1, 5.3, and 5.5: exceptional affine identities -/
namespace AffineDualJT
open scoped BigOperators
open Matrix AffineDetSum
noncomputable section

section Props
variable {F : Type*} [Field F] [CharZero F]
variable {n k : ℕ}

/-- Proposition 5.1 / equation (1.7). -/
theorem prop_5_1_Ct (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedCt x t k = JKEven (k := k) (2*(k:ℤ))
      (fun j y => t^((k:ℤ)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  exact exceptional_Ct_identity x t hn hk hDelta

/-- Proposition 5.3 / equation (1.5). -/
theorem prop_5_3_Bplus (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x ≠ 0) :
    RedBplus x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hPlusKernel (classicalCoefficients x) i m) := by
  exact exceptional_Bplus_identity x t hn hk hDelta

/-- Proposition 5.5 / Theorem B, equation (1.9). -/
theorem prop_5_5_Bt (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedBt x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hHatKernel (classicalCoefficients x) i m) := by
  exact exceptional_Bt_identity x t hn hk hDelta

end Props
end
end AffineDualJT
