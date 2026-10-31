import FidelityLean.MainCertificates
import AffineDualJT.PaperPropositions
import AffineDualJT.ComplementaryMinors

/-! Certificates for the independent finite-dimensional paper statements. -/
noncomputable section
open scoped BigOperators

namespace Fidelity.FiniteBridge
variable {F : Type*} [Field F] {n k : ℕ}

theorem Nt_eq (t : F) (z : Fin n → F) : Spec.Nt t z = AffineDualJT.Nt t z := by
  unfold Spec.Nt AffineDualJT.Nt
  apply Finset.prod_congr rfl
  intro a _
  exact Bridge.prod_ite_eq_prod_subtype (fun b : Fin n => a.val < b.val)
    (fun b => (z a - z b) * (1 - t * z a * z b))

theorem fColumn_eq (t z : F) (r : Fin n) :
    Spec.fColumn t z r = AffineDualJT.fColumn t r z := by
  by_cases h : r.val = 0 <;> simp [Spec.fColumn, AffineDualJT.fColumn, h]

end Fidelity.FiniteBridge

namespace Fidelity.Certificate
open Fidelity.Bridge Fidelity.FiniteBridge

/-- Lemma 2.1 at arbitrary nodes, including zero nodes, over any field. -/
theorem lemma_2_1_general {F : Type*} [Field F] {n : ℕ}
    (t tau : F) (z : Fin n → F) : Spec.Lemma21Interface t tau z := by
  intro _hn
  refine ⟨?_, ?_, ?_⟩
  · simpa only [fColumn_eq, Nt_eq] using AffineDualJT.lemma_2_1_eq_2_3 t z
  · simpa only [Nt_eq] using AffineDualJT.lemma_2_1_eq_2_4 t z
  · simpa only [Nt_eq] using AffineDualJT.lemma_2_1_eq_2_5 tau z

theorem lemma_2_1 (n : ℕ) : Spec.StatementLemma21 n :=
  lemma_2_1_general _ _ _

/-- Theorem 3.1 retains the implementation's universe-polymorphic field range. -/
theorem theorem_3_1_general {F : Type*} [Field F] (n k : ℕ) :
    Spec.Theorem31Interface (F := F) n k := by
  intro _hn _hk X Y U Z hXU hYTZ hXQ0 hUJ hYH hZI
  have h := AffineDualJT.theorem_3_1 X Y U Z hXU hYTZ hXQ0 hUJ hYH hZI
  have hFC : AffineDualJT.firstCols X = X.submatrix id (Spec.initial n k) := by
    ext i j
    rfl
  have hLY : AffineDualJT.lastRowsY Y = Y.submatrix (Spec.tailH n k) id := by
    ext i j
    rfl
  have hTU : AffineDualJT.tailRowsAfterN U = U.submatrix (Spec.tailJ n k) id := by
    ext i j
    rfl
  have hFZ : AffineDualJT.firstRowsZ Z = Z.submatrix (Spec.firstI n k) id := by
    ext i j
    rfl
  rw [hFC, hLY, hTU, hFZ] at h
  simpa only [mul_assoc] using h

theorem theorem_3_1 (n k : ℕ) : Spec.StatementTheorem31 n k := by
  intro F field
  exact theorem_3_1_general n k

end Fidelity.Certificate

namespace Fidelity.FiniteBridge
variable {F : Type*} [Field F] {n k : ℕ}

theorem bracketC_eq (L : ℕ) (m : ℤ) :
    Spec.bracket (F := F) .C L m = AffineDualJT.bracketC (L := L) m := by
  funext p
  simp only [Spec.bracket, ite_apply, Spec.basis, AffineDualJT.bracketC,
    Spec.paperIndex, AffineDualJT.paperIndex, Pi.neg_apply, Pi.zero_apply]
  repeat' (split_ifs <;> simp_all)
  all_goals omega

theorem bracketB_eq (L : ℕ) (m : ℤ) :
    Spec.bracket (F := F) .B L m = AffineDualJT.bracketB (L := L) m := by
  funext p
  simp only [Spec.bracket, ite_apply, Spec.basis, AffineDualJT.bracketB,
    Spec.paperIndex, AffineDualJT.paperIndex, Pi.neg_apply]
  repeat' (split_ifs <;> simp_all)
  all_goals omega

theorem bracketPlus_eq (L : ℕ) (m : ℤ) :
    Spec.bracket (F := F) .plus L m = AffineDualJT.bracketPlus (L := L) m := by
  funext p
  simp only [Spec.bracket, ite_apply, Spec.basis, AffineDualJT.bracketPlus,
    Spec.paperIndex, AffineDualJT.paperIndex]
  repeat' (split_ifs <;> simp_all)
  all_goals omega

theorem Phi_C_eq (x : Fin n → Fˣ) : Spec.Phi (k := k) .C x = AffineDualJT.PhiC x := rfl
theorem Phi_B_eq (x : Fin n → Fˣ) : Spec.Phi (k := k) .B x = AffineDualJT.PhiB x := rfl
theorem Phi_plus_eq (x : Fin n → Fˣ) :
    Spec.Phi (k := k) .plus x = AffineDualJT.PhiPlus x := rfl

theorem columnU_C_eq (t : F) (r : Fin n) :
    Spec.columnU .C k t r = AffineDualJT.uC (k := k) t r := by
  funext p
  by_cases h : r.val = 0 <;>
    simp [Spec.columnU, AffineDualJT.uC, h, bracketC_eq, Bridge.paperIndex_eq]

theorem columnU_B_eq (t : F) (r : Fin n) :
    Spec.columnU .B k t r = AffineDualJT.uB (k := k) t r := by
  funext p
  by_cases h : r.val = 0 <;>
    simp [Spec.columnU, AffineDualJT.uB, h, bracketB_eq, Bridge.paperIndex_eq]

theorem columnU_plus_eq (t : F) (r : Fin n) :
    Spec.columnU .plus k t r = AffineDualJT.uPlus (k := k) t r := by
  funext p
  by_cases h : r.val = 0 <;>
    simp [Spec.columnU, AffineDualJT.uPlus, h, bracketPlus_eq, Bridge.paperIndex_eq]

theorem columnUTilde_C_eq (t : F) (r : Fin n) :
    Spec.columnUTilde .C k t r = AffineDualJT.uCTilde (k := k) t r := by
  funext p
  by_cases h : r.val = 0 <;>
    simp [Spec.columnUTilde, AffineDualJT.uCTilde, h, bracketC_eq, Bridge.paperIndex_eq]

theorem columnUTilde_B_eq (t : F) (r : Fin n) :
    Spec.columnUTilde .B k t r = AffineDualJT.uBTilde (k := k) t r := by
  funext p
  by_cases h : r.val = 0 <;>
    simp [Spec.columnUTilde, AffineDualJT.uBTilde, h, bracketB_eq, Bridge.paperIndex_eq]

theorem V_C0_eq (t tau : F) : Spec.V (n := n) .C0 k t tau = AffineDualJT.VC0 t := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VC0, columnU_C_eq]

theorem V_Ct_eq (t tau : F) : Spec.V (n := n) .Ct k t tau = AffineDualJT.VCt t := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VCt, bracketC_eq, Bridge.paperIndex_eq]

theorem V_BC_eq (t tau : F) : Spec.V (n := n) .BC k t tau = AffineDualJT.VBC tau := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VBC, columnU_C_eq, columnUTilde_C_eq]

theorem V_B0_eq (t tau : F) : Spec.V (n := n) .B0 k t tau = AffineDualJT.VB0 t := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VB0, columnU_B_eq]

theorem V_Bminus_eq (t tau : F) :
    Spec.V (n := n) .Bminus k t tau = AffineDualJT.VBminus tau := by
  ext p r
  simp [Spec.V, AffineDualJT.VBminus, bracketB_eq, Bridge.paperIndex_eq]

theorem V_Bplus_eq (t tau : F) :
    Spec.V (n := n) .Bplus k t tau = AffineDualJT.VBplus t := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VBplus, columnU_plus_eq]

theorem V_Bt_eq (t tau : F) : Spec.V (n := n) .Bt k t tau = AffineDualJT.VBt t := by
  ext p r
  simp [Spec.V, Spec.parameter, AffineDualJT.VBt, columnU_B_eq, columnUTilde_B_eq]

end Fidelity.FiniteBridge

namespace Fidelity.Certificate
open Fidelity.Bridge Fidelity.FiniteBridge

/-- Proposition 2.2, including each complementary minor, with precisely the
paper's positive dimension and positive width assumptions. -/
theorem proposition_2_2 (n k : ℕ) : Spec.StatementProposition22 n k := by
  intro hn hk c
  cases c with
  | C0 =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_C0, Phi_C_eq, V_C0_eq, Delta_C_eq]
      exact AffineDualJT.prop_2_2_C0_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaC_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible n)
    · unfold Spec.FiniteMinor
      rw [V_C0_eq]
      exact AffineDualJT.prop_2_2_minor_VC0 (Spec.symbolicParameter n) hk
  | Ct =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_Ct, Phi_C_eq, V_Ct_eq, Delta_C_eq]
      exact AffineDualJT.prop_2_2_Ct_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaC_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible n)
    · unfold Spec.FiniteMinor
      rw [V_Ct_eq]
      exact AffineDualJT.prop_2_2_minor_VCt (Spec.symbolicParameter n) hk
  | BC =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_BC, Phi_C_eq, V_BC_eq, Delta_C_eq]
      exact AffineDualJT.prop_2_2_BC_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaC_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible_squared n)
    · unfold Spec.FiniteMinor
      rw [V_BC_eq]
      exact AffineDualJT.prop_2_2_minor_VBC (Spec.symbolicParameter n) hk
  | B0 =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_B0, Phi_B_eq, V_B0_eq, Delta_B_eq]
      exact AffineDualJT.prop_2_2_B0_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaB_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible n)
    · unfold Spec.FiniteMinor
      rw [V_B0_eq]
      exact AffineDualJT.prop_2_2_minor_VB0 (Spec.symbolicParameter n) hk
  | Bminus =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_Bminus, Phi_B_eq, V_Bminus_eq, Delta_B_eq]
      exact AffineDualJT.prop_2_2_Bminus_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaB_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible_squared n)
    · unfold Spec.FiniteMinor
      rw [V_Bminus_eq]
      exact AffineDualJT.prop_2_2_minor_VBminus (Spec.symbolicParameter n) hk
  | Bplus =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_Bplus, Phi_plus_eq, V_Bplus_eq, Delta_plus_eq]
      exact AffineDualJT.prop_2_2_Bplus_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaPlus_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible n)
    · unfold Spec.FiniteMinor
      rw [V_Bplus_eq]
      exact AffineDualJT.prop_2_2_minor_VBplus (Spec.symbolicParameter n) hk
  | Bt =>
    constructor
    · unfold Spec.FiniteRatio
      simp only [Spec.caseFolding]
      rw [P_Bt, Phi_B_eq, V_Bt_eq, Delta_B_eq]
      exact AffineDualJT.prop_2_2_Bt_HL (Spec.symbolicX n) (Spec.symbolicParameter n)
        hn hk
        (by simpa only [symbolicX_eq] using AffineDualJT.paper_DeltaB_ne_zero n)
        (by simpa only [symbolicX_eq, symbolicParameter_eq] using AffineDualJT.paper_admissible n)
    · unfold Spec.FiniteMinor
      rw [V_Bt_eq]
      exact AffineDualJT.prop_2_2_minor_VBt (Spec.symbolicParameter n) hk

end Fidelity.Certificate
