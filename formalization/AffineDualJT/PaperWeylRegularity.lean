import AffineDualJT.PaperRegularity
import AffineDualJT.WeylDenominators

/-! # Weyl denominators in the paper's rational function field -/

namespace AffineDualJT
open scoped BigOperators
noncomputable section

theorem paper_Nt_one_ne_zero (n : ℕ) :
    Nt 1 (fun a => (paperVariables n a : PaperField n)) ≠ 0 := by
  classical
  unfold Nt
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  simp only [coe_paperVariables, one_mul]
  exact mul_ne_zero
    (paperVariable_sub_ne_zero a.succ b.val.succ
      (by intro h; exact (show a ≠ b.val from ne_of_lt b.prop) (Fin.succ_injective _ h)))
    (paperVariable_one_sub_mul_ne_zero _ _)

theorem paper_DeltaC_ne_zero (n : ℕ) : DeltaC (paperVariables n) ≠ 0 := by
  classical
  rw [deltaC_product]
  apply mul_ne_zero _ (paper_Nt_one_ne_zero n)
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  simp only [coe_paperVariables]
  exact mul_ne_zero (zpow_ne_zero _ (paperVariable_ne_zero _))
    (paperVariable_one_sub_sq_ne_zero _)

theorem paper_DeltaB_ne_zero (n : ℕ) : DeltaB (paperVariables n) ≠ 0 := by
  classical
  rw [deltaB_product]
  apply mul_ne_zero _ (paper_Nt_one_ne_zero n)
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  simp only [coe_paperVariables]
  exact mul_ne_zero (zpow_ne_zero _ (paperVariable_ne_zero _))
    (paperVariable_one_sub_ne_zero _)

theorem paper_DeltaPlus_ne_zero (n : ℕ) : DeltaPlus (paperVariables n) ≠ 0 := by
  classical
  rw [deltaPlus_product]
  apply mul_ne_zero _ (paper_Nt_one_ne_zero n)
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact zpow_ne_zero _ (Units.ne_zero _)

end
end AffineDualJT
