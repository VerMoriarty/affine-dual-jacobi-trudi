import AffineDualJT.SymmetricPairProducts
import AffineDualJT.FiniteColumnData
import AffineDualJT.ExternalHallLittlewood

/-!
# Reduction of the Weyl sum to the sign sum, source.tex (2.2)

The permutation invariant boundary factors are extracted from the sum,
and the type A symmetrizer supplies `Vn`. The normalization `ν` remains
explicit, so the same reduction applies at width zero.
-/
namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

theorem weylSummand_factor {n : ℕ} (t : F) (k : ℕ) (rho : F → F)
    (z : Fin n → F) : ExternalHL.weylSummand t k rho z =
    (∏ a : Fin n, (z a)⁻¹ ^ k * rho (z a)) *
      pairProduct (fun a b => (1-t*z a*z b)/(1-z a*z b)) *
      pairProduct (fun a b => (t*z a-z b)/(z a-z b)) := by
  classical
  simp only [ExternalHL.weylSummand, pairProduct_subtype, mul_div_mul_comm,
    Finset.prod_mul_distrib]
  ac_rfl

theorem weylSummand_permutation_sum [CharZero F] {n : ℕ} (t : F) (k : ℕ) (rho : F → F)
    (z : Fin n → F) (hz : Function.Injective z) :
    (∑ σ : Equiv.Perm (Fin n), ExternalHL.weylSummand t k rho (z ∘ σ)) =
      ExternalHL.Vn n t * ((∏ a : Fin n, (z a)⁻¹ ^ k * rho (z a)) *
        pairProduct (fun a b => (1-t*z a*z b)/(1-z a*z b))) := by
  classical
  have hs : ∀ a b, (1-t*z a*z b)/(1-z a*z b) =
      (1-t*z b*z a)/(1-z b*z a) := by
    intro a b
    congr 1 <;> ring
  have hrows (σ : Equiv.Perm (Fin n)) := Equiv.prod_comp σ
    (fun a => (z a)⁻¹ ^ k * rho (z a))
  have hpairs (σ : Equiv.Perm (Fin n)) := pairProduct_permutation
    (fun a b => (1-t*z a*z b)/(1-z a*z b)) hs σ
  simp only [weylSummand_factor, Function.comp_apply]
  simp_rw [hrows, hpairs]
  rw [← Finset.mul_sum, symmetrizer z t hz]
  ring

theorem weylSum_eq_reducedWeyl [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ)
    (rho : F → F) (ν : F) (hreg : ExternalHL.Admissible x t ν) :
    ExternalHL.weylSum x t k rho ν = reducedWeyl x t k rho / ν := by
  classical
  have hz (η : Fin n → Bool) : Function.Injective (ExternalHL.signedVariables x η) := by
    intro a b hab
    by_contra hne
    exact hreg.distinct η a b hne (sub_eq_zero.mpr hab)
  have hz0 (η : Fin n → Bool) (a : Fin n) : ExternalHL.signedVariables x η a ≠ 0 := by
    unfold ExternalHL.signedVariables
    split_ifs
    · exact inv_ne_zero (Units.ne_zero _)
    · exact Units.ne_zero _
  unfold ExternalHL.weylSum
  rw [Finset.sum_comm]
  change (∑ η : Fin n → Bool, ∑ σ : Equiv.Perm (Fin n),
    ExternalHL.weylSummand t k rho (ExternalHL.signedVariables x η ∘ σ)) /
      (ExternalHL.Vn n t * ν) = _
  simp_rw [weylSummand_permutation_sum t k rho _ (hz _)]
  rw [← Finset.mul_sum]
  have hnz : ExternalHL.Vn n t ≠ 0 := (mul_ne_zero_iff.mp hreg.normalization).1
  rw [mul_div_mul_left _ _ hnz]
  congr 1
  simp only [reducedWeyl, pairProduct_subtype, ExternalHL.signedVariables]
  rfl

end
end AffineDualJT
