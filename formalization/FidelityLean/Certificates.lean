import FidelityLean.FiniteCertificates
import FidelityLean.FoldingCertificates
import FidelityLean.SequenceCertificates
import FidelityLean.ZeroParameterCertificates
import FidelityLean.DerivedChecks

/-! Closed acceptance types: implementation conclusions cannot be added as
hypotheses without making this module fail to compile. -/
namespace Fidelity.Certificate

theorem accepted_A : ∀ n k : ℕ, Spec.StatementTheoremA n k := theorem_A
theorem accepted_B : ∀ n k : ℕ, Spec.StatementTheoremB n k := theorem_B
theorem accepted_L21 : ∀ n : ℕ, Spec.StatementLemma21 n := lemma_2_1
theorem accepted_P22 : ∀ n k : ℕ, Spec.StatementProposition22 n k := proposition_2_2
theorem accepted_T31 : ∀ n k : ℕ, Spec.StatementTheorem31 n k := theorem_3_1
theorem accepted_L32 : ∀ n k : ℕ, Spec.StatementLemma32 n k := lemma_3_2
theorem accepted_L33 : ∀ (n k : ℕ) (b : Fin k → ℤ → Spec.ParameterField n),
    Spec.StatementLemma33 n k b := lemma_3_3
theorem accepted_P41 : ∀ n k : ℕ, Spec.StatementProposition41 n k := proposition_4_1
theorem accepted_P42 : ∀ n k : ℕ, Spec.StatementProposition42 n k := proposition_4_2
theorem accepted_P51 : ∀ n k : ℕ, Spec.StatementProposition51 n k := proposition_5_1
theorem accepted_L52 : ∀ n k : ℕ, Spec.StatementLemma52 n k := lemma_5_2
theorem accepted_P53 : ∀ n k : ℕ, Spec.StatementProposition53 n k := proposition_5_3
theorem accepted_L54 : ∀ n k : ℕ, Spec.StatementLemma54 n k := lemma_5_4
theorem accepted_P55 : ∀ n k : ℕ, Spec.StatementProposition55 n k := proposition_5_5
theorem accepted_P61 : ∀ n : ℕ, Spec.StatementProposition61 n := proposition_6_1
theorem accepted_C62 : ∀ n k : ℕ, Spec.StatementCorollary62 n k := corollary_6_2
theorem accepted_C62_zero : ∀ n k : ℕ, Spec.Corollary62ZeroSpecializations n k :=
  corollary_6_2_zero

end Fidelity.Certificate
