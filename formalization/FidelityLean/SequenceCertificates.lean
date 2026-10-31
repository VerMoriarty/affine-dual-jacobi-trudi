import FidelityLean.MainCertificates
import AffineDualJT.PaperPropositions
import AffineDualJT.DeterminantFinsum
import AffineDualJT.WeightExponents

noncomputable section
open scoped BigOperators

namespace Fidelity.Bridge
variable {F : Type*} [Field F]

/-- A nonzero-period congruence definition equals the unique-term lattice sum. -/
theorem residueSequence_eq_sum {k : ℕ} (K : ℤ) (hK : K ≠ 0)
    (w : Fin k → ℤ → F) (j : Fin k) (m : ℤ) :
    Spec.residueSequence K w j m =
      ∑ᶠ y : ℤ, if m = Spec.paperIndex j - K * y then w j y else 0 := by
  classical
  by_cases hdiv : (Spec.paperIndex j - m) % K = 0
  · have he := Int.ediv_mul_cancel_of_emod_eq_zero hdiv
    have hm : m = Spec.paperIndex j - K * ((Spec.paperIndex j - m) / K) := by
      linear_combination he
    rw [Spec.residueSequence, ite_eq_left hdiv,
      finsum_eq_single _ ((Spec.paperIndex j - m) / K)]
    · simp only [ite_eq_left hm]
    · intro y hy
      have hn : m ≠ Spec.paperIndex j - K * y := by
        intro h
        apply hy
        apply mul_left_cancel₀ hK
        linear_combination h - hm
      simp only [ite_eq_right hn]
  · have hn (y : ℤ) : m ≠ Spec.paperIndex j - K * y := by
      intro h
      apply hdiv
      have he : Spec.paperIndex j - m = K * y := by linear_combination -h
      simp only [he, Int.mul_emod_right]
    simp only [Spec.residueSequence, ite_eq_right hdiv, hn, ite_false, finsum_zero]

theorem sequence51_eq {k : ℕ} (t : F) (j : Fin k) (m : ℤ) :
    Spec.sequence51 t j m = AffineDualJT.bBplus t j m := by
  have hj := j.isLt
  have hK : 2 * (k : ℤ) ≠ 0 := by omega
  unfold Spec.sequence51 AffineDualJT.bBplus
  rw [residueSequence_eq_sum (2 * (k : ℤ)) hK]
  apply finsum_congr
  intro y
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem Gamma_eq {k : ℕ} (t : F) (j : Fin k) (m : ℤ) :
    Spec.Gamma t j m = AffineDualJT.Gamma t j m := by
  simp only [Spec.Gamma, Spec.sign, sequence51_eq, AffineDualJT.Gamma]

theorem adjacentSequence_eq {k : ℕ} (t : F) (j : Fin k) (m : ℤ) :
    Spec.adjacentSequence t j m = AffineDualJT.aBt t j m := by
  simp only [Spec.adjacentSequence, sequence51_eq, AffineDualJT.aBt]

theorem adjacentC_eq {k : ℕ} (t : F) (j : Fin k) (m : ℤ) :
    Spec.adjacentC t j m = AffineDualJT.cBt t j m := by
  simp only [Spec.adjacentC, Spec.sign, adjacentSequence_eq, AffineDualJT.cBt]

theorem adjacentGamma_eq {k : ℕ} (t : F) (j : Fin k) (m : ℤ) :
    Spec.adjacentGamma t j m = AffineDualJT.gammaBt t j m := by
  simp only [Spec.adjacentGamma, adjacentC_eq, AffineDualJT.gammaBt]
end Fidelity.Bridge

namespace Fidelity.Certificate
open Fidelity.Bridge

theorem lemma_5_2 (n k : ℕ) : Spec.StatementLemma52 n k := by
  intro _hk _ht j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    simpa only [sequence51_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_2_quasiperiod (n := n) j m)
  · intro m
    simpa only [Gamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_2_center (n := n) j m)
  · intro m
    simpa only [Gamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_2_affine (n := n) j m)
  · simpa only [Gamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_2_fixed (n := n) j)

theorem lemma_5_4 (n k : ℕ) : Spec.StatementLemma54 n k := by
  intro _hk _ht j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    simpa only [adjacentC_eq, Gamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_4_eq_5_3 (n := n) j m)
  · intro m
    simpa only [adjacentGamma_eq, Gamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_4_eq_5_4 (n := n) j m)
  · intro m
    simpa only [adjacentGamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_4_eq_5_5 (n := n) j m)
  · simpa only [adjacentGamma_eq, symbolicParameter_eq] using
      (AffineDualJT.paper_lemma_5_4_fixed (n := n) j)

/-- Every exponent is nonnegative on the full integer lattice. -/
theorem parameter_exponents (k : ℕ) : Spec.ParameterExponentsInterface k := by
  intro j y
  simpa only [Spec.expBminus, Spec.expBplus, Spec.expC0, Spec.expCt, Spec.expBC,
    expB0_eq, paperIndex_eq] using
    And.intro (AffineDualJT.B0_exponent_nonneg j y)
      (And.intro (AffineDualJT.Bminus_exponent_nonneg j y)
      (And.intro (AffineDualJT.Bplus_Bt_exponent_nonneg j y)
      (And.intro (AffineDualJT.C0_exponent_nonneg j y)
      (And.intro (AffineDualJT.Ct_exponent_nonneg j y)
        (AffineDualJT.BC_exponent_nonneg j y)))))

/-- The paper's displayed rational half exponent is the exact integer exponent. -/
theorem B0_rational_exponent {k : ℕ} (j : Fin k) (y : ℤ) :
    (Spec.expB0 j y : ℚ) =
      ((k : ℚ) + 1 / 2) * (y : ℚ) ^ 2 -
        ((Spec.paperIndex j : ℚ) - 1 / 2) * (y : ℚ) := by
  simpa only [expB0_eq, paperIndex_eq, Int.cast_natCast] using
    (AffineDualJT.B0_exponent_cast (k : ℤ) (AffineDualJT.paperIndex j) y)

theorem empty_affine {F : Type*} [Field F] : Spec.EmptyAffineInterface (F := F) := by
  intro K w row
  rw [JK_eq, JKEven_eq]
  exact ⟨AffineDualJT.AffineDetSum.JK_zero K w row,
    AffineDualJT.AffineDetSum.JKEven_zero K w row⟩

/-- Zero width has a singleton lattice even when its period is zero. -/
theorem affine_support {F : Type*} [Field F] {k : ℕ} (K : ℤ)
    (w row : Fin k → ℤ → F)
    (hrow : ∀ i, Function.HasFiniteSupport (row i))
    (hK : K ≠ 0 ∨ k = 0) : Spec.AffineFiniteSupport K w row := by
  rcases hK with hK | hk
  · rw [AffineFiniteSupport_eq]
    exact AffineDualJT.AffineDetSum.jkMatrix_det_hasFiniteSupport K hK w row hrow
  · subst k
    let : Unique (Fin 0 → ℤ) :=
      ⟨⟨fun i => Fin.elim0 i⟩, fun _ => Subsingleton.elim _ _⟩
    exact Set.toFinite _

theorem affine_finite_support {F : Type*} [Field F] {n : ℕ}
    (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.AffineFiniteSupportInterface k x t tau := by
  intro _hn
  have hh : ∀ i : Fin k, Function.HasFiniteSupport (Spec.hKernel x i) := by
    intro i
    simpa only [hRow_eq] using
      (AffineDualJT.hKernel_hasFiniteSupport (AffineDualJT.classicalCoefficients x) i)
  have hl : ∀ i : Fin k, Function.HasFiniteSupport (Spec.lambdaKernel x i) := by
    intro i
    simpa only [lambdaRow_eq] using
      (AffineDualJT.lambdaKernel_hasFiniteSupport (AffineDualJT.classicalCoefficients x) i)
  have hp : ∀ i : Fin k, Function.HasFiniteSupport (Spec.hPlusKernel x i) := by
    intro i
    simpa only [hPlusRow_eq] using
      (AffineDualJT.hPlusKernel_hasFiniteSupport (AffineDualJT.classicalCoefficients x) i)
  have ht : ∀ i : Fin k, Function.HasFiniteSupport (Spec.hHatKernel x i) := by
    intro i
    simpa only [hHatRow_eq] using
      (AffineDualJT.hHatKernel_hasFiniteSupport (AffineDualJT.classicalCoefficients x) i)
  have hEven : 2 * (k : ℤ) ≠ 0 ∨ k = 0 := by omega
  refine ⟨affine_support _ _ _ hh (Or.inl (by omega)),
    affine_support _ _ _ hh hEven,
    affine_support _ _ _ hl (Or.inl (by omega)),
    affine_support _ _ _ hl hEven,
    affine_support _ _ _ hl (Or.inl (by omega)), ?_⟩
  intro _hk
  exact ⟨affine_support _ _ _ hp hEven, affine_support _ _ _ ht hEven⟩

end Fidelity.Certificate
