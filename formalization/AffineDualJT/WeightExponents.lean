import AffineDualJT.Basic

/-!
# Integer exponents in (1.3)–(1.9), source.tex §3.3

The division in the `B0` weight is exact, even for negative shifts. The
other exponents are already integer expressions. All weights that can be
evaluated at positive width have nonnegative exponents, as in the paper's
polynomiality argument. This module proves the arithmetic used by the
parameter-polynomial specialization of the affine identities.
-/

namespace AffineDualJT

/-- The integer quadratic inequality used in the paper, with `A=K/2`
and `B=j-η` after clearing a possible denominator. -/
theorem quadratic_exponent_nonneg (A B y : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) :
    0 ≤ A * y ^ 2 - B * y := by
  by_cases hy : y ≤ 0
  · have h₁ := mul_nonneg hA (sq_nonneg y)
    have h₂ := mul_nonpos_of_nonneg_of_nonpos hB hy
    omega
  · have hy1 : 1 ≤ y := by omega
    have h₁ := mul_nonneg hA (show 0 ≤ y ^ 2 - y by nlinarith)
    have h₂ := mul_nonneg (sub_nonneg.mpr hBA) (show 0 ≤ y by omega)
    nlinarith

/-- The numerator in (1.3) is even: the apparent half exponent is an integer. -/
theorem B0_exponent_numerator_even (k j y : ℤ) :
    Even ((2 * k + 1) * y ^ 2 - (2 * j - 1) * y) := by
  have hy : Even (y * (y + 1)) := Int.even_mul_succ_self y
  have he : (2 * k + 1) * y ^ 2 - (2 * j - 1) * y =
      2 * (k * y ^ 2 - j * y) + y * (y + 1) := by ring
  rw [he]
  exact (even_two_mul _).add hy

/-- Exact division certifies that Lean's `ℤ` division does not round (1.3). -/
theorem B0_exponent_exact (k j y : ℤ) :
    2 * (((2 * k + 1) * y ^ 2 - (2 * j - 1) * y) / 2) =
      (2 * k + 1) * y ^ 2 - (2 * j - 1) * y := by
  rw [mul_comm, Int.ediv_mul_cancel (even_iff_two_dvd.mp (B0_exponent_numerator_even k j y))]

/-- The exact integer exponent equals the rational exponent printed in (1.3). -/
theorem B0_exponent_cast (k j y : ℤ) :
    ((((2 * k + 1) * y ^ 2 - (2 * j - 1) * y) / 2 : ℤ) : ℚ) =
      ((k : ℚ) + 1 / 2) * (y : ℚ) ^ 2 - ((j : ℚ) - 1 / 2) * (y : ℚ) := by
  have h := B0_exponent_exact k j y
  have hc := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at hc
  linarith

variable {k : ℕ}

theorem B0_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ ((2 * (k : ℤ) + 1) * y ^ 2 - (2 * paperIndex j - 1) * y) / 2 := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact Int.ediv_nonneg
    (quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)) (by norm_num)

theorem Bminus_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ (2 * (k : ℤ)) * y ^ 2 - (2 * paperIndex j - 1) * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)

theorem Bplus_Bt_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)

/-- In the four affine sums used entrywise in Corollary 6.2, every nonzero
shift has a strictly positive exponent at parameter zero. -/
theorem C0_exponent_pos (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    0 < ((k : ℤ) + 1) * y ^ 2 - paperIndex j * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  have hkz : 0 < (k : ℤ) := by omega
  rw [show ((k : ℤ) + 1) * y ^ 2 - paperIndex j * y =
    y * (((k : ℤ) + 1) * y - paperIndex j) by ring]
  by_cases hp : 0 < y
  · have hy1 : 1 ≤ y := by omega
    have hfactor : 0 < ((k : ℤ) + 1) * y - paperIndex j := by nlinarith
    exact mul_pos (by omega) hfactor
  · have hy1 : y ≤ -1 := by omega
    have hfactor : ((k : ℤ) + 1) * y - paperIndex j < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg (by omega) hfactor

theorem B0_exponent_pos (_hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    0 < ((2 * (k : ℤ) + 1) * y ^ 2 - (2 * paperIndex j - 1) * y) / 2 := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  have hnum : 2 ≤ (2 * (k : ℤ) + 1) * y ^ 2 - (2 * paperIndex j - 1) * y := by
    rw [show (2 * (k : ℤ) + 1) * y ^ 2 - (2 * paperIndex j - 1) * y =
      y * ((2 * (k : ℤ) + 1) * y - (2 * paperIndex j - 1)) by ring]
    by_cases hp : 0 < y
    · have hy1 : 1 ≤ y := by omega
      have hf : 2 ≤ (2 * (k : ℤ) + 1) * y - (2 * paperIndex j - 1) := by nlinarith
      nlinarith
    · have hy1 : y ≤ -1 := by omega
      have hf : (2 * (k : ℤ) + 1) * y - (2 * paperIndex j - 1) ≤ -2 := by nlinarith
      nlinarith
  have heven := B0_exponent_numerator_even (k : ℤ) (paperIndex j) y
  have hdiv : 2 * (((2 * (k : ℤ) + 1) * y ^ 2 -
      (2 * paperIndex j - 1) * y) / 2) =
      (2 * (k : ℤ) + 1) * y ^ 2 - (2 * paperIndex j - 1) * y :=
    B0_exponent_exact (k : ℤ) (paperIndex j) y
  omega

theorem Bplus_Bt_exponent_pos (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    0 < (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  have hkz : 0 < (k : ℤ) := by omega
  rw [show (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y =
    y * ((k : ℤ) * y - (paperIndex j - 1)) by ring]
  by_cases hp : 0 < y
  · have hy1 : 1 ≤ y := by omega
    have hfactor : 0 < (k : ℤ) * y - (paperIndex j - 1) := by nlinarith
    exact mul_pos (by omega) hfactor
  · have hy1 : y ≤ -1 := by omega
    have hfactor : (k : ℤ) * y - (paperIndex j - 1) < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg (by omega) hfactor

/-- The same exponent in the B+ formula (1.5). -/
theorem Bplus_exponent_pos (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    0 < (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y :=
  Bplus_Bt_exponent_pos hk j y hy

/-- The same exponent in the Bt formula (1.9). -/
theorem Bt_exponent_pos (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    0 < (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y :=
  Bplus_Bt_exponent_pos hk j y hy

theorem Ct_exponent_zero_iff (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0) :
    (k : ℤ) * y ^ 2 - paperIndex j * y = 0 ↔ paperIndex j = k ∧ y = 1 := by
  constructor
  · intro he
    have hj := paperIndex_pos j
    have hjk := paperIndex_le j
    have hfactor : y * ((k : ℤ) * y - paperIndex j) = 0 := by
      calc
        y * ((k : ℤ) * y - paperIndex j) = (k : ℤ) * y ^ 2 - paperIndex j * y := by ring
        _ = 0 := he
    have hlin : (k : ℤ) * y = paperIndex j := by
      have hlin' : (k : ℤ) * y - paperIndex j = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hy
      linarith
    have hypos : 0 < y := by
      by_contra h
      have : y ≤ 0 := by omega
      have hprod : (k : ℤ) * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) this
      linarith
    have hy1 : 1 ≤ y := by omega
    have hyEq : y = 1 := by
      by_contra hne
      have htwo : 2 ≤ y := by omega
      nlinarith
    constructor
    · simpa [hyEq] using hlin.symm
    · exact hyEq
  · rintro ⟨hjk, rfl⟩
    rw [hjk]
    ring

theorem C0_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ ((k : ℤ) + 1) * y ^ 2 - paperIndex j * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)

theorem Ct_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ (k : ℤ) * y ^ 2 - paperIndex j * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)

/-- Away from its single boundary exception, the Ct exponent is strictly
positive on nonzero shifts. -/
theorem Ct_exponent_pos_except (hk : 0 < k) (j : Fin k) (y : ℤ) (hy : y ≠ 0)
    (hnot : ¬ (paperIndex j = k ∧ y = 1)) :
    0 < (k : ℤ) * y ^ 2 - paperIndex j * y := by
  have hnonneg := Ct_exponent_nonneg j y
  have hne : (k : ℤ) * y ^ 2 - paperIndex j * y ≠ 0 := by
    intro he
    exact hnot ((Ct_exponent_zero_iff hk j y hy).mp he)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem BC_exponent_nonneg (j : Fin k) (y : ℤ) :
    0 ≤ (2 * (k : ℤ) + 1) * y ^ 2 - 2 * paperIndex j * y := by
  have hj := paperIndex_pos j
  have hjk := paperIndex_le j
  exact quadratic_exponent_nonneg _ _ y (by omega) (by omega) (by omega)

end AffineDualJT
