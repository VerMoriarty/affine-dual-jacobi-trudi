import AffineDualJT.MainIdentities

/-! # Propositions 4.1–4.2 and 5.1/5.3/5.5 with the original Hall–Littlewood left sides -/
namespace AffineDualJT
open AffineDetSum
noncomputable section
variable {F : Type*} [Field F] [CharZero F] {n k : ℕ}

/-- Original Hall–Littlewood form of `prop_4_1_C0`; includes the proved Weyl reduction. -/
theorem prop_4_1_C0_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x t 1) :
    ExternalHL.C0 x t k = JK (k := k) (2*(k:ℤ)+2)
      (fun j y => t^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  rw [bridge_C0 x t hk hreg]
  exact prop_4_1_C0 x t hn hk hDelta

/-- Original Hall–Littlewood form of `prop_4_1_BC`; includes the proved Weyl reduction. -/
theorem prop_4_1_BC_HL (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x (τ^2) 1) :
    ExternalHL.BC x τ k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y * τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  rw [bridge_BC x τ hk hreg]
  exact prop_4_1_BC x τ hn hk hDelta

/-- Original Hall–Littlewood form of `prop_4_2_B0`; includes the proved Weyl reduction. -/
theorem prop_4_2_B0_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x t 1) :
    ExternalHL.B0 x t k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y *
        t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  rw [bridge_B0 x t hk hreg]
  exact prop_4_2_B0 x t hn hk hDelta

/-- Original Hall–Littlewood form of `prop_4_2_Bminus`; includes the proved Weyl reduction. -/
theorem prop_4_2_Bminus_HL (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x (τ^2) 1) :
    ExternalHL.Bminus x τ k = JK (k := k) (2*(k:ℤ))
      (fun j y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  rw [bridge_Bminus x τ hk hreg]
  exact prop_4_2_Bminus x τ hn hk hDelta

/-- Original Hall–Littlewood form of `prop_5_1_Ct`; includes the proved Weyl reduction. -/
theorem prop_5_1_Ct_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x t 1) :
    ExternalHL.Ct x t k = JKEven (k := k) (2*(k:ℤ))
      (fun j y => t^((k:ℤ)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  rw [bridge_Ct x t hk hreg]
  exact prop_5_1_Ct x t hn hk hDelta

/-- Original Hall–Littlewood form of `prop_5_3_Bplus`; includes the proved Weyl reduction. -/
theorem prop_5_3_Bplus_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x ≠ 0) (hreg : ExternalHL.Admissible x t 1) :
    ExternalHL.Bplus x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hPlusKernel (classicalCoefficients x) i m) := by
  rw [bridge_Bplus x t hk hreg]
  exact prop_5_3_Bplus x t hn hk hDelta

/-- Original Hall–Littlewood form of `prop_5_5_Bt`; includes the proved Weyl reduction. -/
theorem prop_5_5_Bt_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x t 1) :
    ExternalHL.Bt x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hHatKernel (classicalCoefficients x) i m) := by
  rw [bridge_Bt x t hk hreg]
  exact prop_5_5_Bt x t hn hk hDelta

end
end AffineDualJT
