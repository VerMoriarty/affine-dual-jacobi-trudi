import AffineDualJT.Basic

/-!
# Monic polynomials for the Weyl denominators, source.tex (2.6)

The paper evaluates its three denominator determinants as Vandermonde
determinants in `z + z⁻¹`.  These are the polynomial families used there.
Dickson polynomials of the second kind give the `C` family; adding the
preceding polynomial gives the `B` family.  The positive-degree first-kind
polynomials give the `+` family, whose constant column is `1`.
-/

namespace AffineDualJT
open Polynomial
noncomputable section

variable {F : Type*} [Field F]

private theorem dickson_degree_data (kind : ℕ) (t : F) : ∀ r : ℕ,
    (dickson kind t r).natDegree ≤ r ∧
    (0 < r → (dickson kind t r).Monic ∧ (dickson kind t r).natDegree = r)
  | 0 => by
    simp only [dickson_zero, ← C_ofNat, ← C_eq_natCast, ← C_sub, natDegree_C]
    simp
  | 1 => by simp
  | r + 2 => by
    obtain ⟨h₀, _⟩ := dickson_degree_data kind t r
    obtain ⟨_, h₁⟩ := dickson_degree_data kind t (r + 1)
    obtain ⟨hm, hd⟩ := h₁ (by omega)
    have hl : (C t * dickson kind t r).natDegree <
        (X * dickson kind t (r + 1)).natDegree := by
      rw [natDegree_X_mul hm.ne_zero, hd]
      have hc := natDegree_mul_le (p := C t) (q := dickson kind t r)
      simp only [natDegree_C, zero_add] at hc
      omega
    have hmonic := (monic_X.mul hm).sub_of_left (degree_lt_degree hl)
    have hdegree : (dickson kind t (r + 2)).natDegree = r + 2 := by
      rw [dickson_add_two, natDegree_sub_eq_left_of_natDegree_lt hl,
        natDegree_X_mul hm.ne_zero, hd]
    exact ⟨hdegree.le, fun _ => ⟨hmonic, hdegree⟩⟩

theorem dickson_monic_natDegree_pos (kind : ℕ) (t : F) (r : ℕ) (hr : 0 < r) :
    (dickson kind t r).Monic ∧ (dickson kind t r).natDegree = r :=
  (dickson_degree_data kind t r).2 hr

/-- The monic polynomial `φ_{r+1}(z)/(z-z⁻¹)`. -/
def weylPolyC (r : ℕ) : F[X] := dickson 2 1 r

/-- The monic polynomial `ψ_{r+1}(z)/(z-1)`. -/
def weylPolyB (r : ℕ) : F[X] :=
  if r = 0 then 1 else dickson 2 1 r + dickson 2 1 (r - 1)

/-- The `χ` columns; the constant column is `1`, while `C₀=2`. -/
def weylPolyPlus (r : ℕ) : F[X] :=
  if r = 0 then 1 else dickson 1 1 r

theorem weylPolyC_monic_degree (r : ℕ) :
    (weylPolyC (F := F) r).Monic ∧ (weylPolyC (F := F) r).natDegree = r := by
  cases r with
  | zero => norm_num [weylPolyC]
  | succ r => exact dickson_monic_natDegree_pos 2 1 _ (by omega)

theorem weylPolyB_monic_degree (r : ℕ) :
    (weylPolyB (F := F) r).Monic ∧ (weylPolyB (F := F) r).natDegree = r := by
  by_cases hr : r = 0
  · subst r; simp [weylPolyB]
  rw [weylPolyB, ite_eq_right hr]
  obtain ⟨hm, hd⟩ := dickson_monic_natDegree_pos 2 (1 : F) r (by omega)
  have hl : (dickson 2 (1 : F) (r - 1)).natDegree < (dickson 2 (1 : F) r).natDegree := by
    rw [hd]
    have h := (dickson_degree_data 2 (1 : F) (r - 1)).1
    omega
  exact ⟨hm.add_of_left (degree_lt_degree hl),
    (natDegree_add_eq_left_of_natDegree_lt hl).trans hd⟩

theorem weylPolyPlus_monic_degree (r : ℕ) :
    (weylPolyPlus (F := F) r).Monic ∧ (weylPolyPlus (F := F) r).natDegree = r := by
  by_cases hr : r = 0
  · subst r; simp [weylPolyPlus]
  rw [weylPolyPlus, ite_eq_right hr]
  exact dickson_monic_natDegree_pos 1 1 r (by omega)

private theorem secondKind_eval (x y : F) (hxy : x * y = 1) : ∀ r : ℕ,
    (x - y) * (dickson 2 (1 : F) r).eval (x + y) = x ^ (r + 1) - y ^ (r + 1)
  | 0 => by norm_num
  | 1 => by simp; ring
  | r + 2 => by
    rw [dickson_add_two]
    simp only [eval_sub, eval_mul, eval_X, C_1, one_mul]
    calc
      (x - y) * ((x + y) * (dickson 2 (1 : F) (r + 1)).eval (x + y) -
          (dickson 2 (1 : F) r).eval (x + y)) =
        (x + y) * ((x - y) * (dickson 2 (1 : F) (r + 1)).eval (x + y)) -
          (x - y) * (dickson 2 (1 : F) r).eval (x + y) := by ring
      _ = (x + y) * (x ^ (r + 2) - y ^ (r + 2)) -
          (x ^ (r + 1) - y ^ (r + 1)) := by
        rw [secondKind_eval x y hxy (r + 1), secondKind_eval x y hxy r]
      _ = x ^ (r + 2 + 1) - y ^ (r + 2 + 1) := by
        simp only [pow_succ]
        linear_combination (x ^ r * x - y ^ r * y) * hxy

private theorem weylPolyB_add_two (r : ℕ) :
    weylPolyB (F := F) (r + 2) = X * weylPolyB (r + 1) - weylPolyB r := by
  cases r with
  | zero => norm_num [weylPolyB, dickson_two]; ring
  | succ r =>
    simp only [weylPolyB, Nat.succ_ne_zero, ite_false]
    change dickson 2 (1 : F) (r + 3) + dickson 2 1 (r + 2) =
      X * (dickson 2 1 (r + 2) + dickson 2 1 (r + 1)) -
        (dickson 2 1 (r + 1) + dickson 2 1 r)
    rw [dickson_add_two 2 1 (r + 1), dickson_add_two 2 1 r]
    simp only [C_1]
    ring

private theorem bKind_eval (x y : F) (hxy : x * y = 1) : ∀ r : ℕ,
    (x - 1) * (weylPolyB (F := F) r).eval (x + y) = x ^ (r + 1) - y ^ r
  | 0 => by simp [weylPolyB]
  | 1 => by
    norm_num [weylPolyB]
    linear_combination hxy
  | r + 2 => by
    rw [weylPolyB_add_two]
    simp only [eval_sub, eval_mul, eval_X]
    calc
      (x - 1) * ((x + y) * (weylPolyB (r + 1)).eval (x + y) -
          (weylPolyB r).eval (x + y)) =
        (x + y) * ((x - 1) * (weylPolyB (r + 1)).eval (x + y)) -
          (x - 1) * (weylPolyB r).eval (x + y) := by ring
      _ = (x + y) * (x ^ (r + 2) - y ^ (r + 1)) - (x ^ (r + 1) - y ^ r) := by
        rw [bKind_eval x y hxy (r + 1), bKind_eval x y hxy r]
      _ = x ^ (r + 2 + 1) - y ^ (r + 2) := by
        simp only [pow_succ]
        linear_combination (x ^ r * x - y ^ r) * hxy

theorem weylPolyC_eval (z : F) (hz : z ≠ 0) (r : ℕ) :
    (z - z⁻¹) * (weylPolyC (F := F) r).eval (z + z⁻¹) =
      z ^ ((r : ℤ) + 1) - z ^ (-((r : ℤ) + 1)) := by
  simpa [weylPolyC, ← zpow_natCast, ← zpow_neg] using
    secondKind_eval z z⁻¹ (mul_inv_cancel₀ hz) r

theorem weylPolyB_eval (z : F) (hz : z ≠ 0) (r : ℕ) :
    (z - 1) * (weylPolyB (F := F) r).eval (z + z⁻¹) =
      z ^ ((r : ℤ) + 1) - z ^ (-(r : ℤ)) := by
  simpa [← zpow_natCast, ← zpow_neg] using
    bKind_eval z z⁻¹ (mul_inv_cancel₀ hz) r

theorem weylPolyPlus_eval (z : F) (hz : z ≠ 0) (r : ℕ) :
    (weylPolyPlus (F := F) r).eval (z + z⁻¹) =
      if r = 0 then 1 else z ^ (r : ℤ) + z ^ (-(r : ℤ)) := by
  by_cases hr : r = 0
  · simp [weylPolyPlus, hr]
  rw [weylPolyPlus, ite_eq_right hr, ite_eq_right hr]
  simpa [← zpow_natCast, ← zpow_neg] using
    dickson_one_one_eval_add_inv z z⁻¹ (mul_inv_cancel₀ hz) r

end
end AffineDualJT
