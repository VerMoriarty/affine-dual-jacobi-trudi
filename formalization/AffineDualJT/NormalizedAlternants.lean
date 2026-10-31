import AffineDualJT.ReducedNumerators

/-! # Normalized alternant numerators with the `C` and `B` boundaries -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

def weightedAlternant (x : Fin n → Fˣ) (b : ℤ) (k : ℕ)
    (c : Fin n → F → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a r => (x a : F)^(b-(k:ℤ))*c r (x a : F)

/-- Cancelling the denominator product leaves precisely one reduced summand. -/
theorem weightedAlternant_ratio (x : Fin n → Fˣ) (t : F) (b : ℤ) (k : ℕ)
    (c : Fin n → F → F) (num den : F → F) (D : F)
    (hD : D≠0)
    (hden : D=(-1:F)^n*(∏ a : Fin n, (x a : F)^b*den (x a : F))*
      Nt 1 (fun a => (x a : F)))
    (hc : (Matrix.of fun a r => c r (x a : F)).det =
      (∏ a : Fin n, num (x a : F))*Nt t (fun a => (x a : F))) :
    (weightedAlternant x b k c).det/D = (-1:F)^n*
      ((∏ a : Fin n, ((x a : F)⁻¹)^k*(num (x a : F)/den (x a : F)))*
      (∏ a : Fin n, ∏ q : {q : Fin n // a<q.val},
        (1-t*(x a : F)*(x q.val : F))/(1-(x a : F)*(x q.val : F)))) := by
  classical
  have hN : Nt 1 (fun a => (x a : F))≠0 := by
    rw [hden] at hD
    exact (mul_ne_zero_iff.mp hD).2
  have hp : (∏ a : Fin n, (x a : F)^b*den (x a : F))≠0 := by
    rw [hden] at hD
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hD).1).2
  have hε : ((-1:F)^n)⁻¹=(-1:F)^n := by rw [← inv_pow,inv_neg,inv_one]
  have hdet : (weightedAlternant x b k c).det =
      (∏ a : Fin n, (x a : F)^(b-(k:ℤ))*num (x a : F))*
        Nt t (fun a => (x a : F)) := by
    have h := det_mul_column (fun a => (x a : F)^(b-(k:ℤ)))
      (Matrix.of fun a r => c r (x a : F))
    rw [hc,← mul_assoc,← Finset.prod_mul_distrib] at h
    exact h
  rw [hdet,hden,mul_div_mul_comm,Nt_ratio t _ hN]
  rw [mul_comm ((-1:F)^n) (∏ a : Fin n, (x a : F)^b*den (x a : F)),
    div_mul_eq_div_mul_one_div,one_div,hε]
  rw [← Finset.prod_div_distrib]
  have hrow (a : Fin n) :
      ((x a : F)^(b-(k:ℤ))*num (x a : F))/((x a : F)^b*den (x a : F)) =
        ((x a : F)⁻¹)^k*(num (x a : F)/den (x a : F)) := by
    rw [mul_div_mul_comm,← zpow_sub₀ (Units.ne_zero _)]
    simp only [show b-(k:ℤ)-b= -(k:ℤ) by ring,_root_.zpow_neg,zpow_natCast,inv_pow]
  simp_rw [hrow]
  ring

end
end AffineDualJT
