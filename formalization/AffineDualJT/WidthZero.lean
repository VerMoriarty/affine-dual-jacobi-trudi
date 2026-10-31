import AffineDualJT.ExternalHallLittlewood
import AffineDualJT.WeylReduction
import AffineDualJT.WeylAdmissibility
import AffineDualJT.WidthZeroReduced

/-!
# Width zero (§6.1, Proposition 6.1)

The seven general-field theorems evaluate the raw rational Weyl sum only
where its denominators are nonzero. The paper-facing statements work in its
symbolic rational-function field. Direct raw evaluation at a singular
normalization factor does not automatically represent cancellation.
-/

namespace AffineDualJT
noncomputable section

variable {F : Type*} [Field F]

/-- Proposition 6.1: all seven normalized width-zero values are `1`. -/
theorem prop_6_1_C0 [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (1)) : ExternalHL.C0 x t 0 = 1 := by
  unfold ExternalHL.C0
  rw [weylSum_eq_reducedWeyl x t 0 _ 1 hreg, div_one]
  exact reduced_C0_width_zero x t (admissible_DeltaC_ne_zero x t 1 hreg)
theorem prop_6_1_Ct [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (ExternalHL.nuCt n 0 t)) : ExternalHL.Ct x t 0 = 1 := by
  unfold ExternalHL.Ct
  rw [weylSum_eq_reducedWeyl x t 0 _ _ hreg]
  change RedCt x t 0 / ExternalHL.nuCt n 0 t = 1
  rw [reduced_Ct_width_zero x t (admissible_DeltaC_ne_zero x t _ hreg)]
  simp only [ExternalHL.nuCt, ite_true]
  exact div_self (by simpa only [ExternalHL.nuCt, ite_true] using
    (mul_ne_zero_iff.mp hreg.normalization).2)
theorem prop_6_1_BC [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (τ : F) (hreg : ExternalHL.Admissible x (τ^2) (1)) : ExternalHL.BC x τ 0 = 1 := by
  unfold ExternalHL.BC
  rw [weylSum_eq_reducedWeyl x (τ^2) 0 _ 1 hreg, div_one]
  exact reduced_BC_width_zero x τ (admissible_DeltaC_ne_zero x (τ^2) 1 hreg)
theorem prop_6_1_B0 [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (1)) : ExternalHL.B0 x t 0 = 1 := by
  unfold ExternalHL.B0
  rw [weylSum_eq_reducedWeyl x t 0 _ 1 hreg, div_one]
  exact reduced_B0_width_zero x t (admissible_DeltaB_ne_zero x t 1 hreg)
theorem prop_6_1_Bminus [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (τ : F) (hreg : ExternalHL.Admissible x (τ^2) (ExternalHL.nuBminus n 0 τ)) : ExternalHL.Bminus x τ 0 = 1 := by
  unfold ExternalHL.Bminus
  rw [weylSum_eq_reducedWeyl x (τ^2) 0 _ _ hreg]
  change RedBminus x τ 0 / ExternalHL.nuBminus n 0 τ = 1
  rw [reduced_Bminus_width_zero x τ (admissible_DeltaB_ne_zero x (τ^2) _ hreg)]
  simp only [ExternalHL.nuBminus, ite_true]
  exact div_self (by simpa only [ExternalHL.nuBminus, ite_true] using
    (mul_ne_zero_iff.mp hreg.normalization).2)
theorem prop_6_1_Bplus [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (ExternalHL.nuBplus n 0 t)) : ExternalHL.Bplus x t 0 = 1 := by
  unfold ExternalHL.Bplus
  rw [weylSum_eq_reducedWeyl x t 0 _ _ hreg]
  change RedBplus x t 0 / ExternalHL.nuBplus n 0 t = 1
  rw [reduced_Bplus_width_zero x t (admissible_DeltaPlus_ne_zero x t _ hreg)]
  simp only [ExternalHL.nuBplus, ite_true]
  exact div_self (by simpa only [ExternalHL.nuBplus, ite_true] using
    (mul_ne_zero_iff.mp hreg.normalization).2)
theorem prop_6_1_Bt [CharZero F] {n : ℕ} (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (ExternalHL.nuCt n 0 t)) : ExternalHL.Bt x t 0 = 1 := by
  unfold ExternalHL.Bt
  rw [weylSum_eq_reducedWeyl x t 0 _ _ hreg]
  change RedBt x t 0 / ExternalHL.nuCt n 0 t = 1
  rw [reduced_Bt_width_zero x t (admissible_DeltaB_ne_zero x t _ hreg)]
  simp only [ExternalHL.nuCt, ite_true]
  exact div_self (by simpa only [ExternalHL.nuCt, ite_true] using
    (mul_ne_zero_iff.mp hreg.normalization).2)

/-- p.2: the literal width-zero continuation of (1.5) would give `1/2`; it is excluded. -/
theorem equation_1_5_width_zero_requires_separate_endpoint [CharZero F] :
    ((2:F)⁻¹) ≠ 1 := by
  norm_num

end
end AffineDualJT
