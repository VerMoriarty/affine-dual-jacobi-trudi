import AffineDualJT.Basic

/-!
# Laurent generating identities for the three coefficient kernels

Integer coefficients are extended by zero before taking `finsum`. Reindexing
these finite sums proves the three generating identities in Lemma 3.2.
Evaluation at `z=-x_a` vanishes because the reciprocal factor for `a`
vanishes. No coefficient identities are assumed as axioms.
-/
open scoped BigOperators
open Polynomial
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F]
theorem intCoeff_finsum_eval (P : F[X]) (z : F) :
    (∑ᶠ r : ℤ, intCoeff P r * z^r) = P.eval z := by
  have hs : Function.support (fun r : ℤ => intCoeff P r * z^r) ⊆
      ↑(P.support.image (fun r : ℕ => (r:ℤ))) := by
    intro r hr
    have hc : intCoeff P r ≠ 0 := left_ne_zero_of_mul hr
    have hn : 0 ≤ r := by
      by_contra h
      exact hc (intCoeff_of_neg P (by omega))
    rw [intCoeff_of_nonneg P hn] at hc
    exact Finset.mem_image.mpr ⟨r.toNat, Polynomial.mem_support_iff.mpr hc,
      Int.toNat_of_nonneg hn⟩
  rw [finsum_eq_finsetSum_of_support_subset _ hs,
    Finset.sum_image (by intro a ha b hb h; exact Int.ofNat_inj.mp h), eval_eq_sum,
    Polynomial.sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [intCoeff_nat, zpow_natCast]

theorem shifted_intCoeff_finsum_eval (P : F[X]) (z : F) (hz : z ≠ 0) (s : ℤ) :
    (∑ᶠ m : ℤ, intCoeff P (s+m) * z^m) = z^(-s) * P.eval z := by
  calc
    _ = ∑ᶠ r : ℤ, intCoeff P r * z^(r-s) := by
      rw [← finsum_comp_equiv (Equiv.addRight (-s : ℤ))]
      apply finsum_congr
      intro r
      change intCoeff P (s+(r+-s)) * z^(r+-s) = intCoeff P r * z^(r-s)
      rw [show s+(r+-s)=r by ring]
      rfl
    _ = z^(-s) * (∑ᶠ r : ℤ, intCoeff P r * z^r) := by
      rw [mul_finsum]
      apply finsum_congr
      intro r
      rw [sub_eq_add_neg, zpow_add₀ hz]
      ring
    _ = _ := by rw [intCoeff_finsum_eval]

theorem dotE_eval_neg_variable {n : ℕ} (x : Fin n → Fˣ) (a : Fin n) :
    (dotE x).eval (-(x a : F)) = 0 := by
  rw [dotE, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [reciprocalFactor]

variable {n k : ℕ}
theorem lambda_generating (x : Fin n → Fˣ) (i : Fin k) (z : F) (hz : z ≠ 0) :
    (∑ᶠ m : ℤ, lambdaKernel (classicalCoefficients x) i m * z^m) =
      z^(-(n:ℤ)) * (dotE x).eval z * (z^(paperIndex i)-z^(-paperIndex i)) := by
  have hA : Function.HasFiniteSupport (fun m =>
      (classicalCoefficients x).eDot ((n:ℤ)-paperIndex i+m) * z^m) :=
    ((classicalCoefficients x).eDot_hasFiniteSupport.fun_comp_of_injective
      (by intro a b h; dsimp at h; omega)).mul_left _
  have hB : Function.HasFiniteSupport (fun m =>
      (classicalCoefficients x).eDot ((n:ℤ)+paperIndex i+m) * z^m) :=
    ((classicalCoefficients x).eDot_hasFiniteSupport.fun_comp_of_injective
      (by intro a b h; dsimp at h; omega)).mul_left _
  simp only [lambdaKernel, sub_mul]
  rw [finsum_sub_distrib hA hB]
  change (∑ᶠ m : ℤ, intCoeff (dotE x) ((n:ℤ)-paperIndex i+m) * z^m) -
    (∑ᶠ m : ℤ, intCoeff (dotE x) ((n:ℤ)+paperIndex i+m) * z^m) = _
  rw [shifted_intCoeff_finsum_eval _ _ hz, shifted_intCoeff_finsum_eval _ _ hz]
  rw [show -((n:ℤ)-paperIndex i) = -(n:ℤ)+paperIndex i by ring,
    show -((n:ℤ)+paperIndex i) = -(n:ℤ)+(-paperIndex i) by ring,
    zpow_add₀ hz, zpow_add₀ hz]
  ring
end
end AffineDualJT

namespace AffineDualJT
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F] {n k : ℕ}
theorem h_center_generating (δ : ℤ) (x : Fin n → Fˣ) (i : Fin k) (z : F) (hz : z ≠ 0) :
    (∑ᶠ m : ℤ, ((classicalCoefficients x).eDot ((n:ℤ)-paperIndex i+m)+
      (classicalCoefficients x).eDot ((n:ℤ)+paperIndex i+m-δ)) * z^m) =
      z^(-(n:ℤ)) * (dotE x).eval z * (z^(paperIndex i)+z^(δ-paperIndex i)) := by
  have hA : Function.HasFiniteSupport (fun m =>
      (classicalCoefficients x).eDot ((n:ℤ)-paperIndex i+m) * z^m) :=
    ((classicalCoefficients x).eDot_hasFiniteSupport.fun_comp_of_injective
      (by intro a b h; dsimp at h; omega)).mul_left _
  have hB : Function.HasFiniteSupport (fun m =>
      (classicalCoefficients x).eDot ((n:ℤ)+paperIndex i+m-δ) * z^m) :=
    ((classicalCoefficients x).eDot_hasFiniteSupport.fun_comp_of_injective
      (by intro a b h; dsimp at h; omega)).mul_left _
  simp only [add_mul]
  rw [finsum_add_distrib hA hB]
  change (∑ᶠ m : ℤ, intCoeff (dotE x) ((n:ℤ)-paperIndex i+m) * z^m) +
    (∑ᶠ m : ℤ, intCoeff (dotE x) ((n:ℤ)+paperIndex i+m-δ) * z^m) = _
  simp_rw [show ∀ m : ℤ, (n:ℤ)+paperIndex i+m-δ = ((n:ℤ)+paperIndex i-δ)+m
    by intro m; ring]
  rw [shifted_intCoeff_finsum_eval _ _ hz, shifted_intCoeff_finsum_eval _ _ hz]
  rw [show -((n:ℤ)-paperIndex i) = -(n:ℤ)+paperIndex i by ring,
    show -((n:ℤ)+paperIndex i-δ) = -(n:ℤ)+(δ-paperIndex i) by ring,
    zpow_add₀ hz, zpow_add₀ hz]
  ring

theorem h_generating (x : Fin n → Fˣ) (i : Fin k) (z : F) (hz : z ≠ 0) :
    (∑ᶠ m : ℤ, hKernel (classicalCoefficients x) i m * z^m) =
      z^(-(n:ℤ)) * (dotE x).eval z * (z^(paperIndex i)+z^(1-paperIndex i)) :=
  h_center_generating 1 x i z hz

theorem hPlus_generating (x : Fin n → Fˣ) (i : Fin k) (z : F) (hz : z ≠ 0) :
    (∑ᶠ m : ℤ, hPlusKernel (classicalCoefficients x) i m * z^m) =
      z^(-(n:ℤ)) * (dotE x).eval z * (z^(paperIndex i)+z^(2-paperIndex i)) :=
  h_center_generating 2 x i z hz
end
end AffineDualJT
