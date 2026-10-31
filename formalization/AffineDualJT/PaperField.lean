import AffineDualJT.HallLittlewoodWeyl

/-! # The coefficient field `ℚ(t,x₁,…,xₙ)` (or `ℚ(τ,x₁,…,xₙ)`). -/
namespace AffineDualJT
noncomputable section
/-- The paper's coefficient field, with coordinate zero for `t` or `τ`. -/
abbrev PaperField (n : ℕ) := FractionRing (MvPolynomial (Fin (n+1)) ℚ)
def paperVariable {n : ℕ} (a : Fin (n+1)) : PaperField n :=
  algebraMap (MvPolynomial (Fin (n+1)) ℚ) (PaperField n) (MvPolynomial.X a)
theorem paperVariable_ne_zero {n : ℕ} (a : Fin (n+1)) : paperVariable a ≠ 0 := by
  intro h
  have hp : (MvPolynomial.X a : MvPolynomial (Fin (n+1)) ℚ) = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin (n+1)) ℚ) (PaperField n) (by simpa only [paperVariable, map_zero] using h)
  exact MvPolynomial.X_ne_zero a hp
def paperParameter (n : ℕ) : PaperField n := paperVariable ⟨0, by omega⟩
def paperVariables (n : ℕ) (a : Fin n) : (PaperField n)ˣ :=
  Units.mk0 (paperVariable a.succ) (paperVariable_ne_zero a.succ)
@[simp] theorem paperParameter_ne_zero (n : ℕ) : paperParameter n ≠ 0 :=
  paperVariable_ne_zero _
@[simp] theorem coe_paperVariables (n : ℕ) (a : Fin n) :
    (paperVariables n a : PaperField n) = paperVariable a.succ := rfl
end
end AffineDualJT

namespace AffineDualJT
noncomputable section
variable {n : ℕ}
theorem paperVariable_sub_ne_zero (a b : Fin (n+1)) (hab : a ≠ b) :
    paperVariable a - paperVariable b ≠ 0 := by
  intro h
  have hp : (MvPolynomial.X a : MvPolynomial (Fin (n+1)) ℚ) = MvPolynomial.X b :=
    IsFractionRing.injective (MvPolynomial (Fin (n+1)) ℚ) (PaperField n) (sub_eq_zero.mp h)
  exact hab (MvPolynomial.X_injective hp)

theorem paperVariable_one_sub_mul_ne_zero (a b : Fin (n+1)) :
    1-paperVariable a*paperVariable b ≠ 0 := by
  intro h
  have hp : (1-MvPolynomial.X a*MvPolynomial.X b : MvPolynomial (Fin (n+1)) ℚ) = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin (n+1)) ℚ) (PaperField n) (by simpa only [paperVariable, map_sub, map_one, map_mul, map_zero] using h)
  have he := congrArg (MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ))) hp
  simp at he

theorem paperVariable_one_sub_ne_zero (a : Fin (n+1)) : 1-paperVariable a ≠ 0 := by
  intro h
  have hp : (1-MvPolynomial.X a : MvPolynomial (Fin (n+1)) ℚ) = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin (n+1)) ℚ) (PaperField n) (by simpa only [paperVariable, map_sub, map_one, map_zero] using h)
  have he := congrArg (MvPolynomial.eval (fun _ : Fin (n+1) => (0:ℚ))) hp
  simp at he

theorem paperVariable_one_sub_sq_ne_zero (a : Fin (n+1)) : 1-paperVariable a^2 ≠ 0 := by
  simpa only [pow_two] using paperVariable_one_sub_mul_ne_zero a a
end
end AffineDualJT
