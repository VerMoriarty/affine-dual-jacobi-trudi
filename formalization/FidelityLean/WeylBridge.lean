import FidelityLean.Spec
import AffineDualJT.ExternalHallLittlewood

/-!
The independent paper Weyl definition and the implementation use different
coordinates for the signs of a signed permutation.  The paper attaches a sign
to the output position `a`; the implementation attaches it to `σ a`.  The
explicit equivalence below reconciles those conventions without changing either
definition.  All statements hold for totalized field operations, so they do not
need a regularity or admissibility assumption.
-/

noncomputable section

open scoped BigOperators

namespace Fidelity.Bridge

variable {F : Type*} [Field F]

/-- Convert signs indexed by positions into signs indexed by variables. -/
def signsReindex {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun η := fun a => η (σ.symm a)
  invFun η := fun a => η (σ a)
  left_inv η := by funext a; simp
  right_inv η := by funext a; simp

@[simp] theorem signsReindex_apply_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (η : Fin n → Bool) (a : Fin n) : signsReindex σ η (σ a) = η a := by
  simp [signsReindex]

/-- The two coordinate conventions give the same point after reindexing. -/
theorem weylPoint_eq {n : ℕ} (x : Fin n → Fˣ)
    (σ : Equiv.Perm (Fin n)) (η : Fin n → Bool) :
    Spec.weylPoint x (σ, η) =
      AffineDualJT.ExternalHL.weylVariables x σ (signsReindex σ η) := by
  funext a
  simp [Spec.weylPoint, AffineDualJT.ExternalHL.weylVariables,
    AffineDualJT.ExternalHL.signedVariables]

/-- A conditional product over all indices equals the product over its subtype. -/
theorem prod_ite_eq_prod_subtype {α M : Type*} [Fintype α] [CommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∏ a, if p a then f a else 1) = ∏ a : {a // p a}, f a.val := by
  classical
  rw [← Finset.prod_filter]
  exact Finset.prod_subtype _ (by simp) f

/-- The paper's conditional pair product is the implementation's subtype product. -/
theorem weylPairProduct_eq {n : ℕ} (t : F) (u : Fin n → F) :
    Spec.weylPairProduct t u =
      ∏ a : Fin n, ∏ b : {b : Fin n // a < b.val},
        ((t * u a - u b.val) * (1 - t * u a * u b.val)) /
          ((u a - u b.val) * (1 - u a * u b.val)) := by
  unfold Spec.weylPairProduct
  apply Finset.prod_congr rfl
  intro a _
  exact
    (prod_ite_eq_prod_subtype (fun b : Fin n => a.val < b.val)
      (fun b => ((t * u a - u b) * (1 - t * u a * u b)) /
        ((u a - u b) * (1 - u a * u b))))

/-- Negative integral powers match powers of the inverse, including at zero. -/
theorem zpow_neg_natCast_eq (u : F) (k : ℕ) : u ^ (-(k : ℤ)) = u⁻¹ ^ k := by
  simp

/-- Pointwise equality before the finite signs are summed. -/
theorem weylSummand_eq {n : ℕ} (c : Spec.PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) (σ : Equiv.Perm (Fin n))
    (η : Fin n → Bool) :
    Spec.weylSummand c k x t tau (σ, η) =
      AffineDualJT.ExternalHL.weylSummand (Spec.parameter c t tau) k
        (Spec.rho c (Spec.parameter c t tau) tau)
        (AffineDualJT.ExternalHL.weylVariables x σ (signsReindex σ η)) := by
  dsimp only [Spec.weylSummand, AffineDualJT.ExternalHL.weylSummand]
  rw [weylPoint_eq, weylPairProduct_eq]
  simp only [zpow_neg_natCast_eq]

/-- The complete finite orbit sum is invariant under the signs equivalence. -/
theorem weylSum_numerator_eq {n : ℕ} (c : Spec.PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) :
    (∑ w : Spec.SignedPermutation n, Spec.weylSummand c k x t tau w) =
      ∑ σ : Equiv.Perm (Fin n), ∑ η : Fin n → Bool,
        AffineDualJT.ExternalHL.weylSummand (Spec.parameter c t tau) k
          (Spec.rho c (Spec.parameter c t tau) tau)
          (AffineDualJT.ExternalHL.weylVariables x σ η) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = ∑ η : Fin n → Bool,
        AffineDualJT.ExternalHL.weylSummand (Spec.parameter c t tau) k
          (Spec.rho c (Spec.parameter c t tau) tau)
          (AffineDualJT.ExternalHL.weylVariables x σ (signsReindex σ η)) := by
      apply Finset.sum_congr rfl
      intro η _
      exact weylSummand_eq c k x t tau σ η
    _ = _ := Equiv.sum_comp (signsReindex σ) (fun η =>
      AffineDualJT.ExternalHL.weylSummand (Spec.parameter c t tau) k
        (Spec.rho c (Spec.parameter c t tau) tau)
        (AffineDualJT.ExternalHL.weylVariables x σ η))

/-- Generic normalized Weyl formula, before specializing its boundary data. -/
theorem P_eq_weylSum {n : ℕ} (c : Spec.PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) :
    Spec.P c k x t tau =
      AffineDualJT.ExternalHL.weylSum x (Spec.parameter c t tau) k
        (Spec.rho c (Spec.parameter c t tau) tau)
        (Spec.nu c n k (Spec.parameter c t tau) tau) := by
  unfold Spec.P AffineDualJT.ExternalHL.weylSum
  rw [weylSum_numerator_eq]
  rfl

/-- Expand the `Ct` and `Bt` width-zero normalization in the paper's indexing. -/
theorem nu_Ct_eq (n k : ℕ) (t tau : F) :
    Spec.nu .Ct n k t tau = AffineDualJT.ExternalHL.nuCt n k t := by
  unfold Spec.nu Spec.nuZero AffineDualJT.ExternalHL.nuCt
    AffineDualJT.ExternalHL.pochhammer
  split_ifs
  · apply Finset.prod_congr rfl
    intro r _
    simp [pow_succ, mul_comm]
  · rfl

/-- The odd powers in the paper's normalization form a Pochhammer product. -/
theorem nu_Bminus_eq (n k : ℕ) (t tau : F) :
    Spec.nu .Bminus n k t tau = AffineDualJT.ExternalHL.nuBminus n k tau := by
  unfold Spec.nu Spec.nuZero AffineDualJT.ExternalHL.nuBminus
    AffineDualJT.ExternalHL.pochhammer
  split_ifs
  · apply Finset.prod_congr rfl
    intro r _
    rw [pow_succ, pow_mul]
    ring
  · rfl

theorem nu_Bplus_eq (n k : ℕ) (t tau : F) :
    Spec.nu .Bplus n k t tau = AffineDualJT.ExternalHL.nuBplus n k t := by
  simp [Spec.nu, Spec.nuZero, AffineDualJT.ExternalHL.nuBplus,
    AffineDualJT.ExternalHL.pochhammer]

theorem P_C0 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .C0 k x t tau = AffineDualJT.ExternalHL.C0 x t k := by
  rw [P_eq_weylSum]
  simp [Spec.parameter, Spec.nu, Spec.nuZero,
    AffineDualJT.ExternalHL.C0]
  rfl

theorem P_Ct {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .Ct k x t tau = AffineDualJT.ExternalHL.Ct x t k := by
  rw [P_eq_weylSum]
  simp only [Spec.parameter, nu_Ct_eq, AffineDualJT.ExternalHL.Ct]
  rfl

theorem P_BC {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .BC k x t tau = AffineDualJT.ExternalHL.BC x tau k := by
  rw [P_eq_weylSum]
  simp [Spec.parameter, Spec.nu, Spec.nuZero,
    AffineDualJT.ExternalHL.BC]
  rfl

theorem P_B0 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .B0 k x t tau = AffineDualJT.ExternalHL.B0 x t k := by
  rw [P_eq_weylSum]
  simp [Spec.parameter, Spec.nu, Spec.nuZero,
    AffineDualJT.ExternalHL.B0]
  rfl

theorem P_Bminus {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .Bminus k x t tau = AffineDualJT.ExternalHL.Bminus x tau k := by
  rw [P_eq_weylSum]
  simp only [Spec.parameter, nu_Bminus_eq,
    AffineDualJT.ExternalHL.Bminus]
  rfl

theorem P_Bplus {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .Bplus k x t tau = AffineDualJT.ExternalHL.Bplus x t k := by
  rw [P_eq_weylSum]
  simp only [Spec.parameter, nu_Bplus_eq,
    AffineDualJT.ExternalHL.Bplus]
  rfl

theorem P_Bt {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) :
    Spec.P .Bt k x t tau = AffineDualJT.ExternalHL.Bt x t k := by
  rw [P_eq_weylSum]
  change AffineDualJT.ExternalHL.weylSum x t k (fun z => (1 - t * z) / (1 - z))
    (Spec.nu .Ct n k t tau) = _
  rw [nu_Ct_eq]
  rfl

end Fidelity.Bridge
