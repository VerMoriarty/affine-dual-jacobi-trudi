import AffineDualJT.PaperField

/-!
# Nonvanishing of the paper's normalization factors

Each rational expression is the image of a multivariate polynomial.
Evaluating all variables at zero proves these polynomials are nonzero;
for `(-1;t)_n` every factor has nonzero constant term, including the first
factor 2. The arguments include zero rank and zero width.
-/
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {n : ℕ}
private theorem mapped_polynomial_ne_zero (P : MvPolynomial (Fin (n+1)) ℚ)
    (hP : P ≠ 0) : algebraMap _ (PaperField n) P ≠ 0 := by
  intro h
  apply hP
  apply IsFractionRing.injective (MvPolynomial (Fin (n+1)) ℚ) (PaperField n)
  simpa only [map_zero] using h

theorem paper_Vn_pow_ne_zero (m d : ℕ) (hd : 0 < d) :
    ExternalHL.Vn m ((paperParameter n)^d) ≠ 0 := by
  let P : MvPolynomial (Fin (n+1)) ℚ :=
    ∏ r : Fin m, ∑ l ∈ Finset.range (r.val+1), (MvPolynomial.X (⟨0,by omega⟩ : Fin (n+1))^d)^l
  have hp : P ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ))) h
    simp [P, zero_pow hd.ne'] at he
  have hm : ExternalHL.Vn m ((paperParameter n)^d) = algebraMap _ (PaperField n) P := by
    simp [ExternalHL.Vn, paperParameter, paperVariable, P, map_prod, map_sum, map_pow]
  rw [hm]
  exact mapped_polynomial_ne_zero P hp

theorem paper_Vn_ne_zero (m : ℕ) : ExternalHL.Vn m (paperParameter n) ≠ 0 := by
  simpa only [pow_one] using paper_Vn_pow_ne_zero (n:=n) m 1 (by norm_num)

theorem paper_pochhammer_Ct_ne_zero (m : ℕ) :
    ExternalHL.pochhammer m (-(paperParameter n)) (paperParameter n) ≠ 0 := by
  let P : MvPolynomial (Fin (n+1)) ℚ := ∏ r : Fin m,
    (1+MvPolynomial.X (⟨0,by omega⟩ : Fin (n+1))^(r.val+1))
  have hp : P ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ))) h
    simp [P] at he
  have hm : ExternalHL.pochhammer m (-(paperParameter n)) (paperParameter n) =
      algebraMap _ (PaperField n) P := by
    simp [ExternalHL.pochhammer, paperParameter, paperVariable, P, map_prod, map_pow, pow_succ, mul_comm]
  rw [hm]
  exact mapped_polynomial_ne_zero P hp

theorem paper_pochhammer_Bminus_ne_zero (m : ℕ) :
    ExternalHL.pochhammer m (paperParameter n) ((paperParameter n)^2) ≠ 0 := by
  let P : MvPolynomial (Fin (n+1)) ℚ := ∏ r : Fin m,
    (1-MvPolynomial.X (⟨0,by omega⟩ : Fin (n+1))^(2*r.val+1))
  have hp : P ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ))) h
    simp [P] at he
  have hm : ExternalHL.pochhammer m (paperParameter n) ((paperParameter n)^2) =
      algebraMap _ (PaperField n) P := by
    simp [ExternalHL.pochhammer, paperParameter, paperVariable, P, map_prod, map_pow,
      pow_succ, pow_mul, mul_pow, mul_comm]
  rw [hm]
  exact mapped_polynomial_ne_zero P hp
end
end AffineDualJT

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {n : ℕ}
theorem paper_pochhammer_Bplus_ne_zero (m : ℕ) :
    ExternalHL.pochhammer m (-1 : PaperField n) (paperParameter n) ≠ 0 := by
  let P : MvPolynomial (Fin (n+1)) ℚ := ∏ r : Fin m,
    (1+MvPolynomial.X (⟨0,by omega⟩ : Fin (n+1))^r.val)
  have he : MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ)) P ≠ 0 := by
    dsimp [P]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    by_cases hz : r.val = 0
    · simp [hz]
    · simp [hz]
  have hp : P ≠ 0 := by
    intro h
    apply he
    rw [h, map_zero]
  have hm : ExternalHL.pochhammer m (-1 : PaperField n) (paperParameter n) =
      algebraMap _ (PaperField n) P := by
    simp [ExternalHL.pochhammer, paperParameter, paperVariable, P, map_prod, map_pow]
  rw [hm]
  exact mapped_polynomial_ne_zero P hp

theorem paper_nuCt_ne_zero (m k : ℕ) : ExternalHL.nuCt m k (paperParameter n) ≠ 0 := by
  unfold ExternalHL.nuCt
  split_ifs
  · exact paper_pochhammer_Ct_ne_zero m
  · exact one_ne_zero

theorem paper_nuBminus_ne_zero (m k : ℕ) : ExternalHL.nuBminus m k (paperParameter n) ≠ 0 := by
  unfold ExternalHL.nuBminus
  split_ifs
  · exact paper_pochhammer_Bminus_ne_zero m
  · exact one_ne_zero

theorem paper_nuBplus_ne_zero (m k : ℕ) : ExternalHL.nuBplus m k (paperParameter n) ≠ 0 := by
  unfold ExternalHL.nuBplus
  split_ifs
  · exact paper_pochhammer_Bplus_ne_zero m
  · exact one_ne_zero
end
end AffineDualJT
