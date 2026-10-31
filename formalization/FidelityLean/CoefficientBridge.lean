import FidelityLean.Spec
import AffineDualJT.AffineDetSum

/-!
The independent paper specification and the coefficient implementation use
the same polynomial products.  The upper cutoff in the specification follows
from the proved degree bounds of the implementation.  The affine sums below
are compared as functions before any finite-support theorem is used.
-/

noncomputable section

open scoped BigOperators

namespace Fidelity.Bridge

theorem paperIndex_eq {k : ℕ} (i : Fin k) :
    Spec.paperIndex i = AffineDualJT.paperIndex i := rfl

section Coefficients

variable {F : Type*} [Field F] {n k : ℕ}

theorem Edot_eq (x : Fin n → Fˣ) : Spec.Edot x = AffineDualJT.dotE x := by
  simp [Spec.Edot, AffineDualJT.dotE, AffineDualJT.reciprocalFactor]

theorem Eddot_eq (x : Fin n → Fˣ) : Spec.Eddot x = AffineDualJT.ddotE x := by
  simp only [Spec.Eddot, AffineDualJT.ddotE, Edot_eq]

theorem dotCoeff_eq (x : Fin n → Fˣ) (r : ℤ) :
    Spec.dotCoeff x r = (AffineDualJT.classicalCoefficients x).eDot r := by
  by_cases hr : r < 0
  · rw [Spec.dotCoeff, ite_eq_right (by omega)]
    exact ((AffineDualJT.classicalCoefficients x).eDot_zero_of_neg r hr).symm
  by_cases hN : r ≤ 2 * (n : ℤ)
  · rw [Spec.dotCoeff, ite_eq_left ⟨by omega, hN⟩, Edot_eq]
    exact (AffineDualJT.intCoeff_of_nonneg _ (by omega)).symm
  · rw [Spec.dotCoeff, ite_eq_right (by omega)]
    exact ((AffineDualJT.classicalCoefficients x).eDot_zero_of_gt r (by omega)).symm

theorem ddotCoeff_eq (x : Fin n → Fˣ) (r : ℤ) :
    Spec.ddotCoeff x r = (AffineDualJT.classicalCoefficients x).eDdot r := by
  by_cases hr : r < 0
  · rw [Spec.ddotCoeff, ite_eq_right (by omega)]
    exact ((AffineDualJT.classicalCoefficients x).eDdot_zero_of_neg r hr).symm
  by_cases hN : r ≤ 2 * (n : ℤ) + 1
  · rw [Spec.ddotCoeff, ite_eq_left ⟨by omega, hN⟩, Eddot_eq]
    exact (AffineDualJT.intCoeff_of_nonneg _ (by omega)).symm
  · rw [Spec.ddotCoeff, ite_eq_right (by omega)]
    exact ((AffineDualJT.classicalCoefficients x).eDdot_zero_of_gt r (by omega)).symm

theorem lambdaKernel_eq (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    Spec.lambdaKernel x i m =
      AffineDualJT.lambdaKernel (AffineDualJT.classicalCoefficients x) i m := by
  simp only [Spec.lambdaKernel, AffineDualJT.lambdaKernel, dotCoeff_eq, paperIndex_eq]

theorem hKernel_eq (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    Spec.hKernel x i m =
      AffineDualJT.hKernel (AffineDualJT.classicalCoefficients x) i m := by
  simp only [Spec.hKernel, AffineDualJT.hKernel, dotCoeff_eq, paperIndex_eq]

theorem hPlusKernel_eq (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    Spec.hPlusKernel x i m =
      AffineDualJT.hPlusKernel (AffineDualJT.classicalCoefficients x) i m := by
  simp only [Spec.hPlusKernel, AffineDualJT.hPlusKernel, dotCoeff_eq, paperIndex_eq]

theorem hHatKernel_eq (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) :
    Spec.hHatKernel x i m =
      AffineDualJT.hHatKernel (AffineDualJT.classicalCoefficients x) i m := by
  simp only [Spec.hHatKernel, AffineDualJT.hHatKernel, ddotCoeff_eq, paperIndex_eq]

theorem sign_eq (m : ℤ) : Spec.sign (F := F) m = (-1 : F) ^ m := rfl

theorem jIntegrand_eq (K : ℤ) (w row : Fin k → ℤ → F) (y : Fin k → ℤ) :
    Spec.jIntegrand K w row y =
      (AffineDualJT.AffineDetSum.jkMatrix K w row y).det := rfl

theorem JK_eq (K : ℤ) (w row : Fin k → ℤ → F) :
    Spec.JK K w row = AffineDualJT.AffineDetSum.JK K w row := rfl

theorem EvenLattice_eq (y : Fin k → ℤ) :
    Spec.EvenLattice y = AffineDualJT.AffineDetSum.EvenVector y := rfl

theorem JKEven_eq (K : ℤ) (w row : Fin k → ℤ → F) :
    Spec.JKEven K w row = AffineDualJT.AffineDetSum.JKEven K w row := by
  classical
  simp only [Spec.JKEven, AffineDualJT.AffineDetSum.JKEven, finsum_eq_if,
    EvenLattice_eq, jIntegrand_eq]
  apply finsum_congr
  intro y
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem JKOn_eq (K : ℤ) (w row : Fin k → ℤ → F)
    (lattice : Set (Fin k → ℤ)) :
    Spec.JKOn K w row lattice =
      AffineDualJT.AffineDetSum.JKOn K w row (fun y => y ∈ lattice) := by
  classical
  simp only [Spec.JKOn, AffineDualJT.AffineDetSum.JKOn, finsum_eq_if, jIntegrand_eq]

theorem AffineFiniteSupport_eq (K : ℤ) (w row : Fin k → ℤ → F) :
    Spec.AffineFiniteSupport K w row =
      Function.HasFiniteSupport
        (fun y => (AffineDualJT.AffineDetSum.jkMatrix K w row y).det) := rfl

end Coefficients

section Weights

variable {F : Type*} [Field F] {k : ℕ}

/-- Moving the integral part outside integer division gives the paper's
printed B0 exponent for every integer lattice shift, including negative ones. -/
theorem expB0_eq (j : Fin k) (y : ℤ) :
    Spec.expB0 j y =
      ((2 * (k : ℤ) + 1) * y ^ 2 -
        (2 * AffineDualJT.paperIndex j - 1) * y) / 2 := by
  unfold Spec.expB0
  rw [paperIndex_eq]
  have hn : (2 * (k : ℤ) + 1) * y ^ 2 -
      (2 * AffineDualJT.paperIndex j - 1) * y =
      (y ^ 2 + y) + ((k : ℤ) * y ^ 2 - AffineDualJT.paperIndex j * y) * 2 := by
    ring
  rw [hn, Int.add_mul_ediv_right]
  · ring
  · norm_num

theorem weightB0_eq (t : F) (j : Fin k) (y : ℤ) :
    Spec.weightB0 t j y = (-1 : F) ^ y *
      t ^ (((2 * (k : ℤ) + 1) * y ^ 2 -
        (2 * AffineDualJT.paperIndex j - 1) * y) / 2) := by
  simp only [Spec.weightB0, sign_eq, expB0_eq]

theorem weightBminus_eq (tau : F) (j : Fin k) (y : ℤ) :
    Spec.weightBminus tau j y =
      tau ^ (2 * (k : ℤ) * y ^ 2 - (2 * AffineDualJT.paperIndex j - 1) * y) := rfl

theorem weightBplus_eq (t : F) (j : Fin k) (y : ℤ) :
    Spec.weightBplus t j y =
      (-1 : F) ^ y * t ^ ((k : ℤ) * y ^ 2 - (AffineDualJT.paperIndex j - 1) * y) := rfl

theorem weightC0_eq (t : F) (j : Fin k) (y : ℤ) :
    Spec.weightC0 t j y =
      t ^ (((k : ℤ) + 1) * y ^ 2 - AffineDualJT.paperIndex j * y) := rfl

theorem weightCt_eq (t : F) (j : Fin k) (y : ℤ) :
    Spec.weightCt t j y =
      t ^ ((k : ℤ) * y ^ 2 - AffineDualJT.paperIndex j * y) := rfl

theorem weightBC_eq (tau : F) (j : Fin k) (y : ℤ) :
    Spec.weightBC tau j y = (-1 : F) ^ y *
      tau ^ ((2 * (k : ℤ) + 1) * y ^ 2 - 2 * AffineDualJT.paperIndex j * y) := rfl

end Weights

end Fidelity.Bridge
