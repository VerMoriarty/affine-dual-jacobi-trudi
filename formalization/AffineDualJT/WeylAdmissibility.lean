import AffineDualJT.HallLittlewoodWeyl
import AffineDualJT.WeylDenominators

/-! # Nonzero Weyl denominators on the admissible evaluation domain -/
namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

theorem admissible_Nt_one_ne_zero (x : Fin n → Fˣ) (t ν : F)
    (hreg : ExternalHL.Admissible x t ν) : Nt 1 (fun a => (x a : F)) ≠ 0 := by
  classical
  unfold Nt
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  simp only [one_mul]
  apply mul_ne_zero
  · simpa only [ExternalHL.signedVariables, Bool.false_eq_true, ite_false] using
      hreg.distinct (fun _ => false) a b.val (ne_of_lt b.property)
  · simpa only [ExternalHL.signedVariables, Bool.false_eq_true, ite_false] using
      hreg.pair (fun _ => false) a b.val (ne_of_lt b.property)

theorem admissible_DeltaC_ne_zero (x : Fin n → Fˣ) (t ν : F)
    (hreg : ExternalHL.Admissible x t ν) : DeltaC x ≠ 0 := by
  classical
  rw [deltaC_product]
  apply mul_ne_zero _ (admissible_Nt_one_ne_zero x t ν hreg)
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply mul_ne_zero (zpow_ne_zero _ (Units.ne_zero _))
  simpa only [ExternalHL.signedVariables, Bool.false_eq_true, ite_false] using
    hreg.boundary (fun _ => false) a

theorem admissible_DeltaB_ne_zero (x : Fin n → Fˣ) (t ν : F)
    (hreg : ExternalHL.Admissible x t ν) : DeltaB x ≠ 0 := by
  classical
  rw [deltaB_product]
  apply mul_ne_zero _ (admissible_Nt_one_ne_zero x t ν hreg)
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply mul_ne_zero (zpow_ne_zero _ (Units.ne_zero _))
  have hb : 1-(x a : F)^2 ≠ 0 := by
    simpa only [ExternalHL.signedVariables, Bool.false_eq_true, ite_false] using
      hreg.boundary (fun _ => false) a
  intro he
  have he1 : (x a : F) = 1 := (sub_eq_zero.mp he).symm
  exact hb (by rw [he1]; ring)

theorem admissible_DeltaPlus_ne_zero (x : Fin n → Fˣ) (t ν : F)
    (hreg : ExternalHL.Admissible x t ν) : DeltaPlus x ≠ 0 := by
  classical
  rw [deltaPlus_product]
  apply mul_ne_zero _ (admissible_Nt_one_ne_zero x t ν hreg)
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact zpow_ne_zero _ (Units.ne_zero _)

end
end AffineDualJT
