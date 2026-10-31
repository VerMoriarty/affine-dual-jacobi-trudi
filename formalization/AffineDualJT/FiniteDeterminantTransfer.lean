import AffineDualJT.FiniteFolding
import AffineDualJT.NormalizedAlternants

/-! # Transfer from a numerator alternant to the finite column determinant -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

/-- The alternant and row folding imply the finite determinant ratio in type `C`. -/
theorem finiteC_from_alternant_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaC x≠0) (c : Fin n → F → F) (num : F → F)
    (V : Matrix (Fin (n+k)) (Fin n) F)
    (hc : ∀ y : Fin n → Fˣ, (Matrix.of fun a r => c r (y a : F)).det =
      (∏ a : Fin n, num (y a : F))*Nt t (fun a => (y a : F)))
    (hfold : ∀ a r,
      (x a : F)^((-(n:ℤ))-(k:ℤ))*c r (x a : F)-
        ((x a : F)⁻¹)^((-(n:ℤ))-(k:ℤ))*c r (x a : F)⁻¹ =
          -(PhiC (k := k) x*V) a r) :
    reducedWeyl x t k (fun z => num z/(1-z^2)) =
      (PhiC (k := k) x*V).det/DeltaC x := by
  classical
  let g : F → Fin n → F := fun z r => z^((-(n:ℤ))-(k:ℤ))*c r z
  have hsum : (∑ η : Fin n → Bool,
      (Matrix.of fun a r => g (invertedVariables x η a : F) r).det/
        DeltaC (invertedVariables x η)) =
      (-1:F)^n*reducedWeyl x t k (fun z => num z/(1-z^2)) := by
    rw [reducedWeyl,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    have h := weightedAlternant_ratio (invertedVariables x η) t (-(n:ℤ)) k c
      num (fun z => 1-z^2) (DeltaC (invertedVariables x η))
      (deltaC_invertedVariables_ne_zero x η hDelta)
      (deltaC_product _) (hc _)
    simpa only [weightedAlternant,g,coe_invertedVariables] using h
  have hinv := inversion_sum_ratio x DeltaC hDelta g
    (fun z => -1) (fun z => -1) (by intro a; norm_num)
    (deltaC_invertedVariables x)
  have hm : (Matrix.of fun a r => g (x a : F) r+(-1)*g (x a : F)⁻¹ r) =
      (-1:F) • (PhiC (k := k) x*V) := by
    ext a r
    simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,one_mul,g,
      neg_mul,sub_eq_add_neg] at *
    exact hfold a r
  rw [hm,Matrix.det_smul,Fintype.card_fin] at hinv
  have h := hsum.symm.trans hinv
  rw [mul_div_assoc] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

/-- The alternant and row folding imply the finite determinant ratio in type `B`. -/

theorem finiteC_from_alternant (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaC x≠0) (c : Fin n → F → F) (num : F → F)
    (V : Matrix (Fin (n+k)) (Fin n) F)
    (hc : ∀ y : Fin n → Fˣ, (Matrix.of fun a r => c r (y a : F)).det =
      (∏ a : Fin n, num (y a : F))*Nt t (fun a => (y a : F)))
    (hfold : ∀ a r,
      (x a : F)^((-(n:ℤ))-(k:ℤ))*c r (x a : F)-
        ((x a : F)⁻¹)^((-(n:ℤ))-(k:ℤ))*c r (x a : F)⁻¹ =
          -(PhiC (k := k) x*V) a r) :
    reducedWeyl x t k (fun z => num z/(1-z^2)) =
      (PhiC (k := k) x*V).det/DeltaC x := finiteC_from_alternant_all_width (k := k) x t hDelta c num V hc hfold

theorem finiteB_from_alternant_all_width (x : Fin n → Fˣ) (t : F)
    (hDelta : DeltaB x≠0) (c : Fin n → F → F) (num : F → F)
    (V : Matrix (Fin (n+k)) (Fin n) F)
    (hc : ∀ y : Fin n → Fˣ, (Matrix.of fun a r => c r (y a : F)).det =
      (∏ a : Fin n, num (y a : F))*Nt t (fun a => (y a : F)))
    (hfold : ∀ a r,
      (x a : F)^((-(n:ℤ)+1)-(k:ℤ))*c r (x a : F)-
        (x a : F)*((x a : F)⁻¹)^((-(n:ℤ)+1)-(k:ℤ))*c r (x a : F)⁻¹ =
          -(PhiB (k := k) x*V) a r) :
    reducedWeyl x t k (fun z => num z/(1-z)) =
      (PhiB (k := k) x*V).det/DeltaB x := by
  classical
  let g : F → Fin n → F := fun z r => z^((-(n:ℤ)+1)-(k:ℤ))*c r z
  have hsum : (∑ η : Fin n → Bool,
      (Matrix.of fun a r => g (invertedVariables x η a : F) r).det/
        DeltaB (invertedVariables x η)) =
      (-1:F)^n*reducedWeyl x t k (fun z => num z/(1-z)) := by
    rw [reducedWeyl,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    have h := weightedAlternant_ratio (invertedVariables x η) t (-(n:ℤ)+1) k c
      num (fun z => 1-z) (DeltaB (invertedVariables x η))
      (deltaB_invertedVariables_ne_zero x η hDelta)
      (deltaB_product _) (hc _)
    simpa only [weightedAlternant,g,coe_invertedVariables] using h
  have hinv := inversion_sum_ratio x DeltaB hDelta g
    (fun z => -z⁻¹) (fun z => -z) (by intro a; simp [Units.ne_zero (x a)])
    (deltaB_invertedVariables x)
  have hm : (Matrix.of fun a r => g (x a : F) r+(-(x a : F))*g (x a : F)⁻¹ r) =
      (-1:F) • (PhiB (k := k) x*V) := by
    ext a r
    simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,one_mul,g,
      neg_mul,mul_assoc,sub_eq_add_neg] at *
    exact hfold a r
  rw [hm,Matrix.det_smul,Fintype.card_fin] at hinv
  have h := hsum.symm.trans hinv
  rw [mul_div_assoc] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

theorem finiteB_from_alternant (x : Fin n → Fˣ) (t : F) (_hk : 0<k)
    (hDelta : DeltaB x≠0) (c : Fin n → F → F) (num : F → F)
    (V : Matrix (Fin (n+k)) (Fin n) F)
    (hc : ∀ y : Fin n → Fˣ, (Matrix.of fun a r => c r (y a : F)).det =
      (∏ a : Fin n, num (y a : F))*Nt t (fun a => (y a : F)))
    (hfold : ∀ a r,
      (x a : F)^((-(n:ℤ)+1)-(k:ℤ))*c r (x a : F)-
        (x a : F)*((x a : F)⁻¹)^((-(n:ℤ)+1)-(k:ℤ))*c r (x a : F)⁻¹ =
          -(PhiB (k := k) x*V) a r) :
    reducedWeyl x t k (fun z => num z/(1-z)) =
      (PhiB (k := k) x*V).det/DeltaB x := finiteB_from_alternant_all_width (k := k) x t hDelta c num V hc hfold

end
end AffineDualJT
