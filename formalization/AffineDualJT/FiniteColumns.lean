import AffineDualJT.FiniteBplus
import AffineDualJT.FiniteCB

/-!
# Proposition 2.2, the seven finite determinant representations

The data are in `FiniteColumnData`; complementary block determinants are
in `FiniteColumnMinors`. Each ratio explicitly requires a nonzero denominator. These theorems concern
the reduced sum (2.2). Identifying it with the Weyl definition (2.1) still
requires the seven `bridge_*` theorems in `MainIdentities`.
-/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Proposition22
variable {F : Type*} [Field F]
variable {n k : ℕ}

/-- Proposition 2.2, case `C0`. -/
theorem prop_2_2_C0 (x : Fin n → Fˣ) (t : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedC0 x t k = (PhiC (k:=k) x * VC0 (n:=n) (k:=k) t).det / DeltaC x := by
  exact finite_c0_ratio x t hk hDelta
/-- Proposition 2.2, case `Ct`. -/
theorem prop_2_2_Ct (x : Fin n → Fˣ) (t : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedCt x t k = (PhiC (k:=k) x * VCt (n:=n) (k:=k) t).det / DeltaC x := by
  exact finite_ct_ratio x t hk hDelta
/-- Proposition 2.2, case `BC`. -/
theorem prop_2_2_BC (x : Fin n → Fˣ) (τ : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaC x ≠ 0) :
    RedBC x τ k = (PhiC (k:=k) x * VBC (n:=n) (k:=k) τ).det / DeltaC x := by
  exact finite_bc_ratio x τ hk hDelta
/-- Proposition 2.2, case `B0`. -/
theorem prop_2_2_B0 (x : Fin n → Fˣ) (t : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedB0 x t k = (PhiB (k:=k) x * VB0 (n:=n) (k:=k) t).det / DeltaB x := by
  exact finite_b0_ratio x t hk hDelta
/-- Proposition 2.2, case `B-`. -/
theorem prop_2_2_Bminus (x : Fin n → Fˣ) (τ : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedBminus x τ k = (PhiB (k:=k) x * VBminus (n:=n) (k:=k) τ).det / DeltaB x := by
  exact finite_bminus_ratio x τ hk hDelta
/-- Proposition 2.2, case `B+`. -/
theorem prop_2_2_Bplus (x : Fin n → Fˣ) (t : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x ≠ 0) :
    RedBplus x t k = (PhiPlus (k:=k) x * VBplus (n:=n) (k:=k) t).det / DeltaPlus x := by
  exact finite_bplus_ratio x t hk hDelta
/-- Proposition 2.2, case `Bt`. -/
theorem prop_2_2_Bt (x : Fin n → Fˣ) (t : F) (_hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) :
    RedBt x t k = (PhiB (k:=k) x * VBt (n:=n) (k:=k) t).det / DeltaB x := by
  exact finite_bt_ratio x t hk hDelta

end Proposition22
end
end AffineDualJT
