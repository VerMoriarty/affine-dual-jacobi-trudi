import FidelityLean.CoefficientBridge
import FidelityLean.WeylBridge
import AffineDualJT.PaperIdentities
import AffineDualJT.PaperSpecializations

/-!
The proof targets in this module are the independent paper specifications.
The existing implementation supplies proofs only after both mathematical
objects and all index/parameter conventions have been bridged explicitly.
-/
noncomputable section
open scoped BigOperators

namespace Fidelity.Bridge

theorem symbolicX_eq (n : ℕ) : Spec.symbolicX n = AffineDualJT.paperVariables n := by
  funext a
  apply Units.ext
  rfl

theorem symbolicParameter_eq (n : ℕ) :
    Spec.symbolicParameter n = AffineDualJT.paperParameter n := rfl

section Rows
variable {F : Type*} [Field F] {n k : ℕ}
theorem lambdaRow_eq (x : Fin n → Fˣ) :
    (Spec.lambdaKernel x : Fin k → ℤ → F) =
      AffineDualJT.lambdaKernel (AffineDualJT.classicalCoefficients x) := by
  funext i m
  exact lambdaKernel_eq x i m
theorem hRow_eq (x : Fin n → Fˣ) :
    (Spec.hKernel x : Fin k → ℤ → F) =
      AffineDualJT.hKernel (AffineDualJT.classicalCoefficients x) := by
  funext i m
  exact hKernel_eq x i m
theorem hPlusRow_eq (x : Fin n → Fˣ) :
    (Spec.hPlusKernel x : Fin k → ℤ → F) =
      AffineDualJT.hPlusKernel (AffineDualJT.classicalCoefficients x) := by
  funext i m
  exact hPlusKernel_eq x i m
theorem hHatRow_eq (x : Fin n → Fˣ) :
    (Spec.hHatKernel x : Fin k → ℤ → F) =
      AffineDualJT.hHatKernel (AffineDualJT.classicalCoefficients x) := by
  funext i m
  exact hHatKernel_eq x i m

theorem Delta_C_eq (x : Fin n → Fˣ) : Spec.Delta .C x = AffineDualJT.DeltaC x := rfl
theorem Delta_B_eq (x : Fin n → Fˣ) : Spec.Delta .B x = AffineDualJT.DeltaB x := rfl
theorem Delta_plus_eq (x : Fin n → Fˣ) : Spec.Delta .plus x = AffineDualJT.DeltaPlus x := rfl
end Rows
end Fidelity.Bridge

namespace Fidelity.Certificate
open Fidelity.Bridge

/-- The original statement, with only its printed dimension conditions. -/
theorem A13 (n k : ℕ) : Spec.StatementA13 n k := by
  intro hn
  have hw : (Spec.weightB0 (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (-1 : Spec.ParameterField n) ^ y * (Spec.symbolicParameter n) ^ (((2 * (k : ℤ) + 1) * y ^ 2 - (2 * AffineDualJT.paperIndex j - 1) * y) / 2)) := by
    funext j y
    exact weightB0_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA13, P_B0, JK_eq, hRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_3 (n := n) (k := k) hn)

/-- The original statement, with only its printed dimension conditions. -/
theorem A14 (n k : ℕ) : Spec.StatementA14 n k := by
  intro hn
  have hw : (Spec.weightBminus (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (Spec.symbolicParameter n) ^ (2 * (k : ℤ) * y ^ 2 - (2 * AffineDualJT.paperIndex j - 1) * y)) := by
    funext j y
    exact weightBminus_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA14, P_Bminus, JK_eq, hRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_4 (n := n) (k := k) hn)

/-- The original statement, with only its printed dimension conditions. -/
theorem A15 (n k : ℕ) : Spec.StatementA15 n k := by
  intro hn hk
  have hw : (Spec.weightBplus (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (-1 : Spec.ParameterField n) ^ y * (Spec.symbolicParameter n) ^ ((k : ℤ) * y ^ 2 - (AffineDualJT.paperIndex j - 1) * y)) := by
    funext j y
    exact weightBplus_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA15, P_Bplus, JK_eq, hPlusRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_5 (n := n) (k := k) hn hk)

/-- The original statement, with only its printed dimension conditions. -/
theorem A16 (n k : ℕ) : Spec.StatementA16 n k := by
  intro hn
  have hw : (Spec.weightC0 (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (Spec.symbolicParameter n) ^ (((k : ℤ) + 1) * y ^ 2 - AffineDualJT.paperIndex j * y)) := by
    funext j y
    exact weightC0_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA16, P_C0, JK_eq, lambdaRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_6 (n := n) (k := k) hn)

/-- The original statement, with only its printed dimension conditions. -/
theorem A17 (n k : ℕ) : Spec.StatementA17 n k := by
  intro hn
  have hw : (Spec.weightCt (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (Spec.symbolicParameter n) ^ ((k : ℤ) * y ^ 2 - AffineDualJT.paperIndex j * y)) := by
    funext j y
    exact weightCt_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA17, P_Ct, JKEven_eq, lambdaRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_7 (n := n) (k := k) hn)

/-- The original statement, with only its printed dimension conditions. -/
theorem A18 (n k : ℕ) : Spec.StatementA18 n k := by
  intro hn
  have hw : (Spec.weightBC (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (-1 : Spec.ParameterField n) ^ y * (Spec.symbolicParameter n) ^ ((2 * (k : ℤ) + 1) * y ^ 2 - 2 * AffineDualJT.paperIndex j * y)) := by
    funext j y
    exact weightBC_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainA18, P_BC, JK_eq, lambdaRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_A_1_8 (n := n) (k := k) hn)

/-- The original statement, with only its printed dimension conditions. -/
theorem B19 (n k : ℕ) : Spec.StatementB19 n k := by
  intro hn hk
  have hw : (Spec.weightBplus (Spec.symbolicParameter n) : Fin k → ℤ → Spec.ParameterField n) =
      (fun j y => (-1 : Spec.ParameterField n) ^ y * (Spec.symbolicParameter n) ^ ((k : ℤ) * y ^ 2 - (AffineDualJT.paperIndex j - 1) * y)) := by
    funext j y
    exact weightBplus_eq (Spec.symbolicParameter n) j y
  rw [Spec.MainB19, P_Bt, JK_eq, hHatRow_eq, hw]
  simpa only [symbolicX_eq, symbolicParameter_eq] using
    (AffineDualJT.paper_theorem_B_1_9 (n := n) (k := k) hn hk)

/-- Seven normalized empty rectangles; the half-factor displays are not used. -/
theorem width_zero (c : Spec.PaperCase) (n : ℕ) : Spec.StatementWidthZero c n := by
  intro hn
  cases c with
  | C0 =>
    simpa only [Spec.WidthZero, P_C0, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_C0 (n := n) hn)
  | Ct =>
    simpa only [Spec.WidthZero, P_Ct, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_Ct (n := n) hn)
  | BC =>
    simpa only [Spec.WidthZero, P_BC, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_BC (n := n) hn)
  | B0 =>
    simpa only [Spec.WidthZero, P_B0, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_B0 (n := n) hn)
  | Bminus =>
    simpa only [Spec.WidthZero, P_Bminus, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_Bminus (n := n) hn)
  | Bplus =>
    simpa only [Spec.WidthZero, P_Bplus, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_Bplus (n := n) hn)
  | Bt =>
    simpa only [Spec.WidthZero, P_Bt, symbolicX_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_prop_6_1_Bt (n := n) hn)

theorem theorem_A (n k : ℕ) : Spec.StatementTheoremA n k := by
  intro hn
  exact ⟨A13 n k hn, A14 n k hn, fun hk => A15 n k hn hk,
    A16 n k hn, A17 n k hn, A18 n k hn, width_zero .Bplus n hn⟩

theorem theorem_B (n k : ℕ) : Spec.StatementTheoremB n k := by
  intro hn
  exact ⟨fun hk => B19 n k hn hk, width_zero .Bt n hn⟩

theorem proposition_4_1 (n k : ℕ) : Spec.StatementProposition41 n k := by
  intro hn _hk
  exact ⟨A16 n k hn, A18 n k hn⟩
theorem proposition_4_2 (n k : ℕ) : Spec.StatementProposition42 n k := by
  intro hn _hk
  exact ⟨A13 n k hn, A14 n k hn⟩
theorem proposition_5_1 (n k : ℕ) : Spec.StatementProposition51 n k := by
  intro hn _hk
  exact A17 n k hn
theorem proposition_5_3 (n k : ℕ) : Spec.StatementProposition53 n k := by
  intro hn hk
  exact A15 n k hn hk
theorem proposition_5_5 (n k : ℕ) : Spec.StatementProposition55 n k := by
  intro hn hk
  exact B19 n k hn hk

theorem proposition_6_1 (n : ℕ) : Spec.StatementProposition61 n := by
  intro hn c
  exact width_zero c n hn

theorem classical_61 (n k : ℕ) : Spec.StatementClassical61 n k := by
  intro hn hk
  simpa only [Spec.Classical61, Spec.classicalNumerator, Spec.phi, Spec.psi,
    Spec.cosine, Delta_C_eq, lambdaKernel_eq, paperIndex_eq, symbolicX_eq,
    AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun] using
    (AffineDualJT.cor_6_2_eq_6_1 (k := k) (AffineDualJT.paperVariables n) hn hk (AffineDualJT.paper_DeltaC_ne_zero n))

theorem classical_62h (n k : ℕ) : Spec.StatementClassical62h n k := by
  intro hn hk
  simpa only [Spec.Classical62h, Spec.classicalNumerator, Spec.phi, Spec.psi,
    Spec.cosine, Delta_B_eq, hKernel_eq, paperIndex_eq, symbolicX_eq,
    AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun] using
    (AffineDualJT.cor_6_2_eq_6_2a (k := k) (AffineDualJT.paperVariables n) hn hk (AffineDualJT.paper_DeltaB_ne_zero n))

theorem classical_62hHat (n k : ℕ) : Spec.StatementClassical62hHat n k := by
  intro hn hk
  simpa only [Spec.Classical62hHat, Spec.classicalNumerator, Spec.phi, Spec.psi,
    Spec.cosine, Delta_B_eq, hHatKernel_eq, paperIndex_eq, symbolicX_eq,
    AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun] using
    (AffineDualJT.cor_6_2_eq_6_2b_ratio (k := k) (AffineDualJT.paperVariables n) hn hk (AffineDualJT.paper_DeltaB_ne_zero n))

theorem classical_63 (n k : ℕ) : Spec.StatementClassical63 n k := by
  intro hn hk
  simpa only [Spec.Classical63, Spec.classicalNumerator, Spec.phi, Spec.psi,
    Spec.cosine, Delta_plus_eq, hPlusKernel_eq, paperIndex_eq, symbolicX_eq,
    AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun] using
    (AffineDualJT.cor_6_2_eq_6_3 (k := k) (AffineDualJT.paperVariables n) hn hk (AffineDualJT.paper_DeltaPlus_ne_zero n))

theorem corollary_6_2 (n k : ℕ) : Spec.StatementCorollary62 n k := by
  intro hn hk
  exact ⟨classical_61 n k hn hk, classical_62h n k hn hk,
    classical_62hHat n k hn hk, classical_63 n k hn hk⟩

end Fidelity.Certificate
