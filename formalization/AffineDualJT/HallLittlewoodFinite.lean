import AffineDualJT.MainIdentities

/-!
# Proposition 2.2 with the original Hall–Littlewood left sides

These statements retain the Weyl-sum definition (2.1). The proved
symmetrizer bridges identify it with the reduced finite ratios in
`FiniteColumns`.
-/
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F] [CharZero F] {n k : ℕ}

/-- Proposition 2.2, case `C0`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_C0_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaC x≠0) (hreg : ExternalHL.Admissible x (t) 1) :
    ExternalHL.C0 x t k =
      (PhiC (k := k) x*VC0 (n := n) (k := k) t).det/DeltaC x := by
  rw [bridge_C0 x t hk hreg]
  exact prop_2_2_C0 x t hn hk hDelta

/-- Proposition 2.2, case `Ct`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_Ct_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaC x≠0) (hreg : ExternalHL.Admissible x (t) 1) :
    ExternalHL.Ct x t k =
      (PhiC (k := k) x*VCt (n := n) (k := k) t).det/DeltaC x := by
  rw [bridge_Ct x t hk hreg]
  exact prop_2_2_Ct x t hn hk hDelta

/-- Proposition 2.2, case `BC`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_BC_HL (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaC x≠0) (hreg : ExternalHL.Admissible x (τ^2) 1) :
    ExternalHL.BC x τ k =
      (PhiC (k := k) x*VBC (n := n) (k := k) τ).det/DeltaC x := by
  rw [bridge_BC x τ hk hreg]
  exact prop_2_2_BC x τ hn hk hDelta

/-- Proposition 2.2, case `B0`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_B0_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaB x≠0) (hreg : ExternalHL.Admissible x (t) 1) :
    ExternalHL.B0 x t k =
      (PhiB (k := k) x*VB0 (n := n) (k := k) t).det/DeltaB x := by
  rw [bridge_B0 x t hk hreg]
  exact prop_2_2_B0 x t hn hk hDelta

/-- Proposition 2.2, case `Bminus`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_Bminus_HL (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaB x≠0) (hreg : ExternalHL.Admissible x (τ^2) 1) :
    ExternalHL.Bminus x τ k =
      (PhiB (k := k) x*VBminus (n := n) (k := k) τ).det/DeltaB x := by
  rw [bridge_Bminus x τ hk hreg]
  exact prop_2_2_Bminus x τ hn hk hDelta

/-- Proposition 2.2, case `Bplus`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_Bplus_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaPlus x≠0) (hreg : ExternalHL.Admissible x (t) 1) :
    ExternalHL.Bplus x t k =
      (PhiPlus (k := k) x*VBplus (n := n) (k := k) t).det/DeltaPlus x := by
  rw [bridge_Bplus x t hk hreg]
  exact prop_2_2_Bplus x t hn hk hDelta

/-- Proposition 2.2, case `Bt`, including the Weyl-to-reduced bridge. -/
theorem prop_2_2_Bt_HL (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k)
    (hDelta : DeltaB x≠0) (hreg : ExternalHL.Admissible x (t) 1) :
    ExternalHL.Bt x t k =
      (PhiB (k := k) x*VBt (n := n) (k := k) t).det/DeltaB x := by
  rw [bridge_Bt x t hk hreg]
  exact prop_2_2_Bt x t hn hk hDelta

end
end AffineDualJT
