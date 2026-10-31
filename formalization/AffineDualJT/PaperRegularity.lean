import AffineDualJT.PaperNormalizations
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {n : ℕ}
theorem signed_paper_distinct (η : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) :
    ExternalHL.signedVariables (paperVariables n) η a -
      ExternalHL.signedVariables (paperVariables n) η b ≠ 0 := by
  have he : a.succ ≠ b.succ := by intro h; exact hab (Fin.succ_injective _ h)
  have hdiff := paperVariable_sub_ne_zero a.succ b.succ he
  have hpair := paperVariable_one_sub_mul_ne_zero a.succ b.succ
  have ha := paperVariable_ne_zero a.succ
  have hb := paperVariable_ne_zero b.succ
  simp only [ExternalHL.signedVariables, coe_paperVariables]
  cases hηa : η a <;> cases hηb : η b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hdiff
  · intro h
    field_simp [ha,hb] at h
    apply hpair
    linear_combination -h
  · intro h
    field_simp [ha,hb] at h
    apply hpair
    simpa using h
  · intro h
    field_simp [ha,hb] at h
    apply hdiff
    linear_combination -h

theorem signed_paper_pair (η : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) :
    1-ExternalHL.signedVariables (paperVariables n) η a *
      ExternalHL.signedVariables (paperVariables n) η b ≠ 0 := by
  have he : a.succ ≠ b.succ := by intro h; exact hab (Fin.succ_injective _ h)
  have hdiff := paperVariable_sub_ne_zero a.succ b.succ he
  have hpair := paperVariable_one_sub_mul_ne_zero a.succ b.succ
  have ha := paperVariable_ne_zero a.succ
  have hb := paperVariable_ne_zero b.succ
  simp only [ExternalHL.signedVariables, coe_paperVariables]
  cases hηa : η a <;> cases hηb : η b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hpair
  · intro h
    field_simp [ha,hb] at h
    apply hdiff
    linear_combination -h
  · intro h
    field_simp [ha,hb] at h
    exact hdiff (by simpa using h)
  · intro h
    field_simp [ha,hb] at h
    apply hpair
    linear_combination -h

theorem signed_paper_boundary (η : Fin n → Bool) (a : Fin n) :
    1-(ExternalHL.signedVariables (paperVariables n) η a)^2 ≠ 0 := by
  have hsq := paperVariable_one_sub_sq_ne_zero a.succ
  have ha := paperVariable_ne_zero a.succ
  simp only [ExternalHL.signedVariables, coe_paperVariables]
  cases hηa : η a <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hsq
  · intro h
    field_simp [ha] at h
    apply hsq
    linear_combination -h
end
end AffineDualJT

namespace AffineDualJT
noncomputable section
variable {n : ℕ}
/-- Independence of the `x` coordinates supplies the common rational-expression domain. -/
theorem paper_admissible_of_normalization (t ν : PaperField n)
    (hnorm : ExternalHL.Vn n t * ν ≠ 0) : ExternalHL.Admissible (paperVariables n) t ν :=
  ⟨hnorm, signed_paper_distinct, signed_paper_pair, signed_paper_boundary⟩

/-- The common positive-width normalization for `C0`, `B0`, `Ct`, `Bplus`, and `Bt`. -/
theorem paper_admissible (n : ℕ) :
    ExternalHL.Admissible (paperVariables n) (paperParameter n) 1 :=
  paper_admissible_of_normalization _ _ (by simpa only [mul_one] using paper_Vn_ne_zero n)

/-- The square-root cases use `t=τ²`. -/
theorem paper_admissible_squared (n : ℕ) :
    ExternalHL.Admissible (paperVariables n) ((paperParameter n)^2) 1 :=
  paper_admissible_of_normalization _ _
    (by simpa only [mul_one] using paper_Vn_pow_ne_zero n 2 (by norm_num))

/-- The boundary normalization for `Ct` and `Bt`, including empty rectangles. -/
theorem paper_admissible_Ct (n k : ℕ) :
    ExternalHL.Admissible (paperVariables n) (paperParameter n)
      (ExternalHL.nuCt n k (paperParameter n)) :=
  paper_admissible_of_normalization _ _
    (mul_ne_zero (paper_Vn_ne_zero n) (paper_nuCt_ne_zero n k))

/-- The boundary normalization for `Bminus`, including empty rectangles. -/
theorem paper_admissible_Bminus (n k : ℕ) :
    ExternalHL.Admissible (paperVariables n) ((paperParameter n)^2)
      (ExternalHL.nuBminus n k (paperParameter n)) :=
  paper_admissible_of_normalization _ _
    (mul_ne_zero (paper_Vn_pow_ne_zero n 2 (by norm_num)) (paper_nuBminus_ne_zero n k))

/-- The boundary normalization for `Bplus`, including its separate empty endpoint. -/
theorem paper_admissible_Bplus (n k : ℕ) :
    ExternalHL.Admissible (paperVariables n) (paperParameter n)
      (ExternalHL.nuBplus n k (paperParameter n)) :=
  paper_admissible_of_normalization _ _
    (mul_ne_zero (paper_Vn_ne_zero n) (paper_nuBplus_ne_zero n k))
end
end AffineDualJT
