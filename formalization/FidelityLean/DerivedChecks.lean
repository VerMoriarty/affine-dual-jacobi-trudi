import AffineDualJT.ExceptionalSequences
import AffineDualJT.FiniteColumnEvaluation

/-!
Supplementary certificates for paper proof atoms which were not separately
named in the original implementation.  These declarations reuse the original
mathematical definitions, without changing the frozen independent paper spec.
Their build/acceptance status is recorded outside this source file.
-/

noncomputable section
open scoped BigOperators
open AffineDualJT

namespace Fidelity.Derived

variable {F : Type*} [Field F]

/-- Paper §5.1, fixed residue, for every integer q (not only the head q=0). -/
theorem Ct_fixed_residue {k : ℕ} (hk : 0 < k) (t : F) (j : Fin k)
    (hj : paperIndex j = (k : ℤ)) (q : ℤ) :
    cCt t j ((k : ℤ) + 2 * (k : ℤ) * q) =
      (2 : F) * (-1 : F) ^ q * t ^ ((k : ℤ) * q * (q + 1)) := by
  have hb (r : ℤ) :
      bCt t j (paperIndex j + 2 * (k : ℤ) * r) =
        (-1 : F) ^ r * t ^ ((k : ℤ) * r ^ 2 + paperIndex j * r) := by
    exact residue_point_eq (2 * (k : ℤ)) (paperIndex j) (by omega)
      (fun r => (-1 : F) ^ r * t ^ ((k : ℤ) * r ^ 2 + paperIndex j * r)) r
  have hm : -((k : ℤ) + 2 * (k : ℤ) * q) =
      paperIndex j + 2 * (k : ℤ) * (-q - 1) := by
    rw [hj]
    ring
  have hneg (m : ℤ) : (-1 : F) ^ (-m) = (-1 : F) ^ m := by
    simp only [← Int.cast_negOnePow F, Int.negOnePow_neg]
  have hs : (-1 : F) ^ (-q - 1) = -((-1 : F) ^ q) := by
    rw [show -q - 1 = -(q + 1) by ring, hneg,
      zpow_add₀ (by norm_num : (-1 : F) ≠ 0), zpow_one]
    ring
  have hb1 : bCt t j ((k : ℤ) + 2 * (k : ℤ) * q) =
      (-1 : F) ^ q * t ^ ((k : ℤ) * q ^ 2 + (k : ℤ) * q) := by
    simpa only [hj] using hb q
  have hb2 : bCt t j (-((k : ℤ) + 2 * (k : ℤ) * q)) =
      (-1 : F) ^ (-q - 1) * t ^ ((k : ℤ) * (-q - 1) ^ 2 + (k : ℤ) * (-q - 1)) := by
    rw [hm]
    simpa only [hj] using hb (-q - 1)
  unfold cCt
  rw [hb1, hb2, hs]
  rw [show (k : ℤ) * q ^ 2 + (k : ℤ) * q = (k : ℤ) * q * (q + 1) by ring,
    show (k : ℤ) * (-q - 1) ^ 2 + (k : ℤ) * (-q - 1) =
      (k : ℤ) * q * (q + 1) by ring]
  ring

/-- Equation (5.1) is zero outside its single residue class. -/
theorem bBplus_zero_outside {k : ℕ} (t : F) (j : Fin k) (m : ℤ)
    (hm : ¬ (2 * (k : ℤ)) ∣ (m - paperIndex j)) : bBplus t j m = 0 := by
  have hne (y : ℤ) : m ≠ paperIndex j - 2 * (k : ℤ) * y := by
    intro he
    apply hm
    refine ⟨-y, ?_⟩
    rw [he]
    ring
  simp only [bBplus, hne, ite_false, finsum_zero]

/-- Lemma 5.4: the adjacent sequence vanishes away from classes j and j-1. -/
theorem aBt_zero_outside_adjacent {k : ℕ} (t : F) (j : Fin k) (m : ℤ)
    (h₁ : ¬ (2 * (k : ℤ)) ∣ (m - paperIndex j))
    (h₂ : ¬ (2 * (k : ℤ)) ∣ (m - (paperIndex j - 1))) : aBt t j m = 0 := by
  have h₂' : ¬ (2 * (k : ℤ)) ∣ ((m + 1) - paperIndex j) := by
    simpa only [show m + 1 - paperIndex j = m - (paperIndex j - 1) by ring] using h₂
  rw [aBt, bBplus_zero_outside t j m h₁, bBplus_zero_outside t j (m + 1) h₂']
  simp

/-- The full integer support of aBt, stated as a subset of two residue classes. -/
theorem aBt_support_adjacent {k : ℕ} (t : F) (j : Fin k) :
    Function.support (aBt t j) ⊆
      {m : ℤ | (2 * (k : ℤ)) ∣ (m - paperIndex j) ∨
        (2 * (k : ℤ)) ∣ (m - (paperIndex j - 1))} := by
  intro m hm
  by_cases h₁ : (2 * (k : ℤ)) ∣ (m - paperIndex j)
  · exact Or.inl h₁
  · by_cases h₂ : (2 * (k : ℤ)) ∣ (m - (paperIndex j - 1))
    · exact Or.inr h₂
    · exact False.elim (hm (aBt_zero_outside_adjacent t j m h₁ h₂))

/-- Width-zero Bt: the finite evaluated column is the difference of u and t utilde. -/
theorem widthZero_Bt_column {n : ℕ} (x : Fin n → Fˣ) (t : F)
    (a r : Fin n) :
    (PhiB (k := 0) x * VBt (n := n) (k := 0) t) a r =
      (if r.val = 0 then psi 1 (x a : F) else
        psi (paperIndex r) (x a : F) + t ^ r.val * psi (2 - paperIndex r) (x a : F)) -
      t * (if r.val = 0 then psi 0 (x a : F) else
        psi (paperIndex r - 1) (x a : F) + t ^ r.val * psi (1 - paperIndex r) (x a : F)) := by
  have he : (PhiB (k := 0) x * VBt (n := n) (k := 0) t) a r =
      (∑ p : Fin (n + 0), PhiB x a p * uB (n := n) (k := 0) t r p) -
      t * ∑ p : Fin (n + 0), PhiB x a p * uBTilde (n := n) (k := 0) t r p := by
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [VBt]
    ring
  rw [PhiB_uB_apply_all_width, PhiB_uBTilde_apply_all_width] at he
  norm_num only [Nat.cast_zero, zero_add, add_zero, add_sub_cancel_right] at he
  exact he

/-- Proposition 6.1: Bt's first width-zero column is (1+t) psi_1. -/
theorem widthZero_Bt_firstcolumn {n : ℕ} (x : Fin n → Fˣ) (t : F)
    (a r : Fin n) (hr : r.val = 0) :
    (PhiB (k := 0) x * VBt (n := n) (k := 0) t) a r =
      (1 + t) * psi 1 (x a : F) := by
  rw [widthZero_Bt_column]
  simp only [hr, ite_true]
  rw [show (0 : ℤ) = 1 - 1 by ring, psi_reflect]
  ring

/-- Proposition 6.1: paper column r=paperIndex r≥2 of Bt at width zero. -/
theorem widthZero_Bt_restcolumns {n : ℕ} (x : Fin n → Fˣ) (t : F)
    (a r : Fin n) (hr : r.val ≠ 0) :
    (PhiB (k := 0) x * VBt (n := n) (k := 0) t) a r =
      (1 + t ^ (r.val + 1)) * psi (paperIndex r) (x a : F) -
        (t + t ^ r.val) * psi (paperIndex r - 1) (x a : F) := by
  rw [widthZero_Bt_column]
  simp only [hr, ite_false]
  rw [show 2 - paperIndex r = 1 - (paperIndex r - 1) by ring,
    psi_reflect, psi_reflect, pow_succ]
  ring

/-- Width-zero BC: evaluation of u^C+tau utilde^C before reflection. -/
theorem widthZero_BC_column {n : ℕ} (x : Fin n → Fˣ) (τ : F)
    (a r : Fin n) :
    (PhiC (k := 0) x * VBC (n := n) (k := 0) τ) a r =
      (if r.val = 0 then phi 1 (x a : F) else
        phi (paperIndex r) (x a : F) + (τ ^ 2) ^ r.val * phi (2 - paperIndex r) (x a : F)) +
      τ * (if r.val = 0 then phi 0 (x a : F) else
        phi (paperIndex r - 1) (x a : F) + (τ ^ 2) ^ r.val * phi (1 - paperIndex r) (x a : F)) := by
  have he : (PhiC (k := 0) x * VBC (n := n) (k := 0) τ) a r =
      (∑ p : Fin (n + 0), PhiC x a p * uC (n := n) (k := 0) (τ ^ 2) r p) +
      τ * ∑ p : Fin (n + 0), PhiC x a p * uCTilde (n := n) (k := 0) (τ ^ 2) r p := by
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [VBC]
    ring
  rw [PhiC_uC_apply_all_width, PhiC_uCTilde_apply_all_width] at he
  norm_num only [Nat.cast_zero, zero_add, add_zero, add_sub_cancel_right] at he
  exact he

/-- Proposition 6.1: BC's first width-zero column is phi_1. -/
theorem widthZero_BC_firstcolumn {n : ℕ} (x : Fin n → Fˣ) (τ : F)
    (a r : Fin n) (hr : r.val = 0) :
    (PhiC (k := 0) x * VBC (n := n) (k := 0) τ) a r = phi 1 (x a : F) := by
  rw [widthZero_BC_column]
  simp [hr, phi]

/-- Proposition 6.1: paper column r=paperIndex r≥2 of BC at width zero. -/
theorem widthZero_BC_restcolumns {n : ℕ} (x : Fin n → Fˣ) (τ : F)
    (a r : Fin n) (hr : r.val ≠ 0) :
    (PhiC (k := 0) x * VBC (n := n) (k := 0) τ) a r =
      phi (paperIndex r) (x a : F) +
        (τ - τ ^ (2 * r.val + 1)) * phi (paperIndex r - 1) (x a : F) -
        τ ^ (2 * r.val) * phi (paperIndex r - 2) (x a : F) := by
  rw [widthZero_BC_column]
  simp only [hr, ite_false]
  rw [show 2 - paperIndex r = -(paperIndex r - 2) by ring,
    show 1 - paperIndex r = -(paperIndex r - 1) by ring, phi_neg, phi_neg,
    pow_succ, pow_mul]
  ring

/-- Palindromic alternative for h in §3.2, with all integer indices. -/
theorem h_palindrome_form {n k : ℕ} (c : CoeffSystem F n) (i : Fin k) (m : ℤ) :
    hKernel c i m = c.eDot ((n : ℤ) - paperIndex i + m) +
      c.eDot ((n : ℤ) - paperIndex i - m + 1) := by
  unfold hKernel
  congr 1
  rw [← c.eDot_pal ((n : ℤ) + paperIndex i + m - 1)]
  congr 1
  ring

/-- Palindromic alternative for h+ in §3.2. -/
theorem hPlus_palindrome_form {n k : ℕ} (c : CoeffSystem F n) (i : Fin k) (m : ℤ) :
    hPlusKernel c i m = c.eDot ((n : ℤ) - paperIndex i + m) +
      c.eDot ((n : ℤ) - paperIndex i - m + 2) := by
  unfold hPlusKernel
  congr 1
  rw [← c.eDot_pal ((n : ℤ) + paperIndex i + m - 2)]
  congr 1
  ring

/-- Four endpoint coefficients used by the paper's triangular normalizations. -/
theorem coefficient_endpoints {n : ℕ} (x : Fin n → Fˣ) :
    let c := classicalCoefficients x
    c.eDot 0 = 1 ∧ c.eDot (2 * (n : ℤ)) = 1 ∧
      c.eDdot 0 = 1 ∧ c.eDdot (2 * (n : ℤ) + 1) = 1 := by
  dsimp only
  let c := classicalCoefficients x
  have h0 : c.eDot 0 = 1 := classicalCoefficients_eDot_zero x
  have hN : c.eDot (2 * (n : ℤ)) = 1 := by
    simpa using (c.eDot_pal 0).trans h0
  have hd0 : c.eDdot 0 = 1 := by
    rw [c.eDdot_eq, h0, zero_sub, c.eDot_zero_of_neg (-1) (by omega)]
    ring
  have hdN : c.eDdot (2 * (n : ℤ) + 1) = 1 := by
    simpa using (c.eDdot_pal 0).trans hd0
  exact ⟨h0, hN, hd0, hdN⟩

end Fidelity.Derived
