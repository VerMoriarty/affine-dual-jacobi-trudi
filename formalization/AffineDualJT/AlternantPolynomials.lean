import AffineDualJT.WeylPolynomials

/-!
# Polynomial columns for Lemma 2.1

For `y=z⁻¹+t*z`, the polynomial evaluations give the row factors used
to prove proportionality under the reciprocal substitution in Lemma 2.1.
The first-kind constant column is normalized to `1`, as in `f₁`.
-/

namespace AffineDualJT
open Polynomial
noncomputable section
variable {F : Type*} [Field F]

def alternantPolyBasic (t : F) (r : ℕ) : F[X] :=
  if r = 0 then 1 else dickson 1 t r

def alternantPolyCt (t : F) (r : ℕ) : F[X] := dickson 2 t r

def alternantPolyBminus (τ : F) (r : ℕ) : F[X] :=
  if r = 0 then 1 else dickson 2 (τ^2) r - C τ * dickson 2 (τ^2) (r-1)

theorem dickson_first_eval (t x y : F) (hxy : x*y = t) : ∀ r : ℕ,
    (dickson 1 t r).eval (x+y) = x^r + y^r
  | 0 => by norm_num
  | 1 => by simp
  | r+2 => by
    rw [dickson_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    rw [dickson_first_eval t x y hxy (r+1), dickson_first_eval t x y hxy r]
    simp only [pow_succ]
    linear_combination (x^r + y^r)*hxy

theorem dickson_second_eval (t x y : F) (hxy : x*y = t) : ∀ r : ℕ,
    (x-y)*(dickson 2 t r).eval (x+y) = x^(r+1)-y^(r+1)
  | 0 => by norm_num
  | 1 => by simp; ring
  | r+2 => by
    rw [dickson_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    calc
      (x-y)*((x+y)*(dickson 2 t (r+1)).eval (x+y)-
          t*(dickson 2 t r).eval (x+y)) =
        (x+y)*((x-y)*(dickson 2 t (r+1)).eval (x+y))-
          t*((x-y)*(dickson 2 t r).eval (x+y)) := by ring
      _ = (x+y)*(x^(r+2)-y^(r+2))-t*(x^(r+1)-y^(r+1)) := by
        rw [dickson_second_eval t x y hxy (r+1), dickson_second_eval t x y hxy r]
      _ = x^(r+2+1)-y^(r+2+1) := by
        simp only [pow_succ]
        linear_combination (x^r*x-y^r*y)*hxy

private theorem alternantPolyBminus_add_two (τ : F) (r : ℕ) :
    alternantPolyBminus τ (r+2) =
      X * alternantPolyBminus τ (r+1) - C (τ^2) * alternantPolyBminus τ r := by
  cases r with
  | zero => norm_num [alternantPolyBminus, dickson_two]; ring
  | succ r =>
    simp only [alternantPolyBminus, Nat.succ_ne_zero, ite_false]
    change dickson 2 (τ^2) (r+3) - C τ * dickson 2 (τ^2) (r+2) =
      X * (dickson 2 (τ^2) (r+2) - C τ * dickson 2 (τ^2) (r+1)) -
        C (τ^2) * (dickson 2 (τ^2) (r+1) - C τ * dickson 2 (τ^2) r)
    rw [dickson_add_two 2 (τ^2) (r+1), dickson_add_two 2 (τ^2) r]
    ring

theorem alternantPolyBasic_eval (t z : F) (hz : z ≠ 0) (r : ℕ) :
    (alternantPolyBasic t r).eval (z⁻¹+t*z) =
      if r = 0 then 1 else z^(-(r:ℤ)) + t^r*z^(r:ℤ) := by
  by_cases hr : r = 0
  · simp [alternantPolyBasic, hr]
  rw [alternantPolyBasic, ite_eq_right hr, ite_eq_right hr]
  have hxy : z⁻¹*(t*z) = t := by field_simp
  simpa only [inv_pow, mul_pow, zpow_natCast, zpow_neg] using
    dickson_first_eval t z⁻¹ (t*z) hxy r

theorem alternantPolyCt_eval (t z : F) (hz : z ≠ 0) (r : ℕ) :
    (1-t*z^2)*(alternantPolyCt t r).eval (z⁻¹+t*z) =
      z^(-(r:ℤ)) - t^(r+1)*z^((r:ℤ)+2) := by
  have hxy : z⁻¹*(t*z) = t := by field_simp
  have h := dickson_second_eval t z⁻¹ (t*z) hxy r
  have he : 1-t*z^2 = z*(z⁻¹-t*z) := by field_simp
  rw [he, mul_assoc, show alternantPolyCt t r = dickson 2 t r from rfl, h]
  simp only [mul_sub, inv_pow, mul_pow]
  simp only [← zpow_natCast z, ← zpow_neg z]
  have hx : z*z^(-((r+1:ℕ):ℤ)) = z^(-(r:ℤ)) := by
    calc
      _ = z^(1+(-((r+1:ℕ):ℤ))) := by rw [zpow_add₀ hz, zpow_one]
      _ = _ := by rw [show 1+(-((r+1:ℕ):ℤ)) = -(r:ℤ) by omega]
  have hy : z*(t^(r+1)*z^((r+1:ℕ):ℤ)) = t^(r+1)*z^((r:ℤ)+2) := by
    calc
      _ = t^(r+1)*(z*z^((r+1:ℕ):ℤ)) := by ring
      _ = t^(r+1)*z^(1+((r+1:ℕ):ℤ)) := by rw [zpow_add₀ hz, zpow_one]
      _ = _ := by rw [show 1+((r+1:ℕ):ℤ) = (r:ℤ)+2 by omega]
  rw [hx, hy]

theorem alternantPolyBminus_eval (τ z : F) (hz : z ≠ 0) : ∀ r : ℕ,
    (1+τ*z)*(alternantPolyBminus τ r).eval (z⁻¹+τ^2*z) =
      z^(-(r:ℤ)) + τ^(2*r+1)*z^((r:ℤ)+1)
  | 0 => by simp [alternantPolyBminus]
  | 1 => by
    norm_num [alternantPolyBminus]
    field_simp
    ring
  | r+2 => by
    rw [alternantPolyBminus_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    calc
      (1+τ*z)*((z⁻¹+τ^2*z)*(alternantPolyBminus τ (r+1)).eval (z⁻¹+τ^2*z)-
          τ^2*(alternantPolyBminus τ r).eval (z⁻¹+τ^2*z)) =
        (z⁻¹+τ^2*z)*((1+τ*z)*(alternantPolyBminus τ (r+1)).eval (z⁻¹+τ^2*z))-
          τ^2*((1+τ*z)*(alternantPolyBminus τ r).eval (z⁻¹+τ^2*z)) := by ring
      _ = (z⁻¹+τ^2*z)*(z^(-((r+1:ℕ):ℤ))+τ^(2*(r+1)+1)*z^(((r+1:ℕ):ℤ)+1))-
          τ^2*(z^(-(r:ℤ))+τ^(2*r+1)*z^((r:ℤ)+1)) := by
        rw [alternantPolyBminus_eval τ z hz (r+1), alternantPolyBminus_eval τ z hz r]
      _ = z^(-((r+2:ℕ):ℤ)) + τ^(2*(r+2)+1)*z^(((r+2:ℕ):ℤ)+1) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        rw [show -((r:ℤ)+1) = -(r:ℤ)-1 by ring,
          show -((r:ℤ)+2) = -(r:ℤ)-2 by ring]
        simp only [zpow_sub₀ hz, zpow_add₀ hz, zpow_one, zpow_two, pow_succ]
        field_simp
        ring

end
end AffineDualJT
