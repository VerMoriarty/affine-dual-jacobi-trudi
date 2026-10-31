import FidelityLean.MainCertificates
import AffineDualJT.Folding

/-!
Certificates for Lemmas 3.2 and 3.3 of the independent specification.  The
bridges retain the paper's one-based indices and identify the signed rows,
ordered tail minor, and three folded sequences before using the proved
kernel and folding identities.
-/

noncomputable section

open scoped BigOperators

namespace Fidelity.FoldingBridge

variable {F : Type*} [Field F] {n k : ℕ}

theorem Phi_C_eq (x : Fin n → Fˣ) :
    Spec.Phi (k := k) .C x = AffineDualJT.PhiC (k := k) x := rfl

theorem Phi_B_eq (x : Fin n → Fˣ) :
    Spec.Phi (k := k) .B x = AffineDualJT.PhiB (k := k) x := rfl

theorem Phi_plus_eq (x : Fin n → Fˣ) :
    Spec.Phi (k := k) .plus x = AffineDualJT.PhiPlus (k := k) x := rfl

theorem paperSign_eq_pow {L : ℕ} (p : Fin L) :
    Spec.sign (F := F) (AffineDualJT.paperIndex p) = (-1 : F) ^ (p.val + 1) := by
  simpa only [Spec.sign, AffineDualJT.paperIndex, Nat.cast_add, Nat.cast_one] using
    (zpow_natCast (-1 : F) (p.val + 1))

theorem D_C_eq (x : Fin n → Fˣ) :
    Spec.D (k := k) .C x =
      AffineDualJT.DC (k := k) (AffineDualJT.classicalCoefficients x) := by
  ext p i
  simp only [Spec.D, paperSign_eq_pow, Bridge.lambdaKernel_eq, Bridge.paperIndex_eq,
    AffineDualJT.DC, AffineDualJT.rowSign]

theorem D_B_eq (x : Fin n → Fˣ) :
    Spec.D (k := k) .B x =
      AffineDualJT.DB (k := k) (AffineDualJT.classicalCoefficients x) := by
  ext p i
  simp only [Spec.D, paperSign_eq_pow, Bridge.hKernel_eq, Bridge.paperIndex_eq,
    AffineDualJT.DB, AffineDualJT.rowSign]

theorem D_plus_eq (x : Fin n → Fˣ) :
    Spec.D (k := k) .plus x =
      AffineDualJT.DPlus (k := k) (AffineDualJT.classicalCoefficients x) := by
  ext p i
  simp only [Spec.D, paperSign_eq_pow, Bridge.hPlusKernel_eq, Bridge.paperIndex_eq,
    AffineDualJT.DPlus, AffineDualJT.rowSign]

theorem folded_C_eq (b : Fin k → ℤ → F) :
    Spec.foldedSequence .C (n + k) b = AffineDualJT.CC (n := n) b := rfl

theorem folded_B_eq (b : Fin k → ℤ → F) :
    Spec.foldedSequence .B (n + k) b = AffineDualJT.CB (n := n) b := by
  ext p j
  simp only [Spec.foldedSequence, paperSign_eq_pow, Bridge.paperIndex_eq, AffineDualJT.CB]

theorem folded_plus_eq (b : Fin k → ℤ → F) :
    Spec.foldedSequence .plus (n + k) b = AffineDualJT.CPlus (n := n) b := by
  ext p j
  simp only [Spec.foldedSequence, paperSign_eq_pow, Bridge.paperIndex_eq,
    AffineDualJT.CPlus]

omit [Field F] in
theorem tailRows_eq (M : Matrix (Fin (n + k)) (Fin k) F) :
    M.submatrix (Spec.tailJ n k) id = AffineDualJT.tailRowsAfterN M := rfl

theorem omega_eq (k : ℕ) : Spec.omega (F := F) k = AffineDualJT.omegaSign F k := rfl

theorem zeta_eq (n k : ℕ) : Spec.zeta (F := F) n k = AffineDualJT.zetaSign F n k := rfl

theorem lemma32 (x : Fin n → Fˣ) : Spec.Lemma32Interface k x := by
  intro _hn hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d
    cases d with
    | C =>
      simpa only [Phi_C_eq, D_C_eq] using
        (AffineDualJT.lemma_3_2_PhiC_DC (k := k) x)
    | B =>
      simpa only [Phi_B_eq, D_B_eq] using
        (AffineDualJT.lemma_3_2_PhiB_DB (k := k) x)
    | plus =>
      simpa only [Phi_plus_eq, D_plus_eq] using
        (AffineDualJT.lemma_3_2_PhiPlus_DPlus (k := k) x)
  · simpa only [D_C_eq, tailRows_eq, zeta_eq] using
      (AffineDualJT.lemma_3_2_minor_DC (k := k) x)
  · simpa only [D_B_eq, tailRows_eq, zeta_eq] using
      (AffineDualJT.lemma_3_2_minor_DB (k := k) x)
  · simpa only [D_plus_eq, tailRows_eq, zeta_eq] using
      (AffineDualJT.lemma_3_2_minor_DPlus (k := k) x hk)

theorem lemma33 (x : Fin n → Fˣ) (b : Fin k → ℤ → F) :
    Spec.Lemma33Interface k x b := by
  intro _hn _hk i j
  refine ⟨?_, ?_, ?_⟩
  · simpa only [D_C_eq, folded_C_eq, Bridge.sign_eq, Bridge.lambdaKernel_eq] using
      (AffineDualJT.lemma_3_3_eq_3_5 (AffineDualJT.classicalCoefficients x) b i j)
  · simpa only [D_B_eq, folded_B_eq, Bridge.hKernel_eq] using
      (AffineDualJT.lemma_3_3_eq_3_6 (AffineDualJT.classicalCoefficients x) b i j)
  · simpa only [D_plus_eq, folded_plus_eq, Bridge.hPlusKernel_eq] using
      (AffineDualJT.lemma_3_3_eq_3_7 (AffineDualJT.classicalCoefficients x) b i j)

end Fidelity.FoldingBridge

namespace Fidelity.Certificate

theorem lemma_3_2 (n k : ℕ) : Spec.StatementLemma32 n k :=
  FoldingBridge.lemma32 (Spec.symbolicX n)

theorem lemma_3_3 (n k : ℕ) (b : Fin k → ℤ → Spec.ParameterField n) :
    Spec.StatementLemma33 n k b :=
  FoldingBridge.lemma33 (Spec.symbolicX n) b

end Fidelity.Certificate
