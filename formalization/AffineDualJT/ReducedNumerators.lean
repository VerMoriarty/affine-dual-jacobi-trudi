import AffineDualJT.SignedDeterminants

/-! # Clearing the finite Weyl denominator in the reduced sign sum -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n : ℕ}

theorem Nt_one_pair_ne_zero (z : Fin n → F) (hN : Nt 1 z≠0)
    (a : Fin n) (b : {b : Fin n // a<b.val}) :
    (z a-z b.val)*(1-z a*z b.val)≠0 := by
  classical
  have ha := Finset.prod_ne_zero_iff.mp hN a (Finset.mem_univ _)
  have hb := Finset.prod_ne_zero_iff.mp ha b (Finset.mem_univ _)
  simpa only [one_mul] using hb

theorem Nt_ratio (t : F) (z : Fin n → F) (hN : Nt 1 z≠0) :
    Nt t z/Nt 1 z =
      ∏ a : Fin n, ∏ b : {b : Fin n // a<b.val},
        (1-t*z a*z b.val)/(1-z a*z b.val) := by
  classical
  unfold Nt
  simp only [one_mul]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro b _
  exact mul_div_mul_left _ _ ((mul_ne_zero_iff.mp (Nt_one_pair_ne_zero z hN a b)).1)

def basicWeightedMatrix (x : Fin n → Fˣ) (t : F) (k : ℕ) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a r => (x a : F)^(-((n:ℤ)+(k:ℤ)-1))*fColumn t r (x a : F)

theorem basicWeightedMatrix_det (x : Fin n → Fˣ) (t : F) (k : ℕ) :
    (basicWeightedMatrix x t k).det =
      (∏ a : Fin n, (x a : F)^(-((n:ℤ)+(k:ℤ)-1)))*Nt t (fun a => (x a : F)) := by
  have h := det_mul_column (fun a => (x a : F)^(-((n:ℤ)+(k:ℤ)-1)))
    (Matrix.of fun a r : Fin n => fColumn t r (x a : F))
  rw [lemma_2_1_eq_2_3_of t _] at h
  exact h

theorem basicWeightedMatrix_plus_ratio (x : Fin n → Fˣ) (t : F) (k : ℕ)
    (hDelta : DeltaPlus x≠0) :
    (basicWeightedMatrix x t k).det/DeltaPlus x =
      (∏ a : Fin n, ((x a : F)⁻¹)^k) *
        (∏ a : Fin n, ∏ b : {b : Fin n // a<b.val},
          (1-t*(x a : F)*(x b.val : F))/(1-(x a : F)*(x b.val : F))) := by
  classical
  have hN : Nt 1 (fun a => (x a : F))≠0 := by
    rw [deltaPlus_product] at hDelta
    exact (mul_ne_zero_iff.mp hDelta).2
  rw [basicWeightedMatrix_det,deltaPlus_product,mul_div_mul_comm]
  rw [← Finset.prod_div_distrib,Nt_ratio t _ hN]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [← zpow_sub₀ (Units.ne_zero (x a)),
    show -((n:ℤ)+(k:ℤ)-1)-(-(n:ℤ)+1)= -(k:ℤ) by ring]
  simp only [_root_.zpow_neg,zpow_natCast,inv_pow]

end
end AffineDualJT
