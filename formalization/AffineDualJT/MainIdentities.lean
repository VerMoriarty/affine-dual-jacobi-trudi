import AffineDualJT.ClassicalSpecialization
import AffineDualJT.Section4Ordinary
import AffineDualJT.Section5Exceptional
import AffineDualJT.ExternalHallLittlewood
import AffineDualJT.WeylReduction
import AffineDualJT.WidthZero

/-!
# Theorem A and Theorem B

The positive-width algebraic identities are obtained in §§4--5 for the
reduced Weyl sums. The bridges below follow from the proved symmetrizer
reduction of the explicit Weyl-sum definition (2.1) to (2.2).
Generic evaluation requires `ExternalHL.Admissible`; the symbolic variables
of the paper satisfy it by `PaperRegularity`.
-/

namespace AffineDualJT
open AffineDetSum
noncomputable section

section Bridges
variable {F : Type*} [Field F]
variable {n k : ℕ}

/-- Present paper pp.3--5, equation (2.2) + Proposition 2.2; external convention from [7]. -/
theorem bridge_C0 [CharZero F] (x : Fin n → Fˣ) (t : F) (_hk : 0<k) (hreg : ExternalHL.Admissible x t 1) : ExternalHL.C0 x t k = RedC0 x t k := by
  simpa only [ExternalHL.C0, RedC0, div_one] using
    weylSum_eq_reducedWeyl x t k (fun z => (1-z^2)⁻¹) 1 hreg
theorem bridge_Ct [CharZero F] (x : Fin n → Fˣ) (t : F) (hk : 0<k) (hreg : ExternalHL.Admissible x t 1) : ExternalHL.Ct x t k = RedCt x t k := by
  simpa only [ExternalHL.Ct, RedCt, ExternalHL.nuCt, ite_eq_right hk.ne', div_one] using
    weylSum_eq_reducedWeyl x t k (fun z => (1-t*z^2)/(1-z^2)) 1 hreg
theorem bridge_BC [CharZero F] (x : Fin n → Fˣ) (τ : F) (_hk : 0<k) (hreg : ExternalHL.Admissible x (τ^2) 1) : ExternalHL.BC x τ k = RedBC x τ k := by
  simpa only [ExternalHL.BC, RedBC, div_one] using
    weylSum_eq_reducedWeyl x (τ^2) k (fun z => (1+τ*z)/(1-z^2)) 1 hreg
theorem bridge_B0 [CharZero F] (x : Fin n → Fˣ) (t : F) (_hk : 0<k) (hreg : ExternalHL.Admissible x t 1) : ExternalHL.B0 x t k = RedB0 x t k := by
  simpa only [ExternalHL.B0, RedB0, div_one] using
    weylSum_eq_reducedWeyl x t k (fun z => (1-z)⁻¹) 1 hreg
theorem bridge_Bminus [CharZero F] (x : Fin n → Fˣ) (τ : F) (hk : 0<k) (hreg : ExternalHL.Admissible x (τ^2) 1) : ExternalHL.Bminus x τ k = RedBminus x τ k := by
  simpa only [ExternalHL.Bminus, RedBminus, ExternalHL.nuBminus, ite_eq_right hk.ne', div_one] using
    weylSum_eq_reducedWeyl x (τ^2) k (fun z => (1+τ*z)/(1-z)) 1 hreg
theorem bridge_Bplus [CharZero F] (x : Fin n → Fˣ) (t : F) (hk : 0<k) (hreg : ExternalHL.Admissible x t 1) : ExternalHL.Bplus x t k = RedBplus x t k := by
  simpa only [ExternalHL.Bplus, RedBplus, ExternalHL.nuBplus, ite_eq_right hk.ne', div_one] using
    weylSum_eq_reducedWeyl x t k (fun _ => 1) 1 hreg
theorem bridge_Bt [CharZero F] (x : Fin n → Fˣ) (t : F) (hk : 0<k) (hreg : ExternalHL.Admissible x t 1) : ExternalHL.Bt x t k = RedBt x t k := by
  simpa only [ExternalHL.Bt, RedBt, ExternalHL.nuCt, ite_eq_right hk.ne', div_one] using
    weylSum_eq_reducedWeyl x t k (fun z => (1-t*z)/(1-z)) 1 hreg

end Bridges

section Main
variable {F : Type*} [Field F] [CharZero F]
variable {n k : ℕ}

/-- Theorem A, equation (1.3), p.2. -/
theorem theorem_A_1_3 (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x t (1)) :
    ExternalHL.B0 x t k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y * t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  by_cases hk0 : k = 0
  · subst k
    rw [prop_6_1_B0 x t hreg]
    simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [bridge_B0 x t hk hreg]
    exact prop_4_2_B0 x t hn hk hDelta

/-- Theorem A, equation (1.4), p.2. -/
theorem theorem_A_1_4 (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x (τ^2) (ExternalHL.nuBminus n k τ)) :
    ExternalHL.Bminus x τ k = JK (k := k) (2*(k:ℤ))
      (fun j y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (fun i m => hKernel (classicalCoefficients x) i m) := by
  by_cases hk0 : k = 0
  · subst k
    rw [prop_6_1_Bminus x τ hreg]
    simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hr : ExternalHL.Admissible x (τ^2) 1 := by
      simpa only [ExternalHL.nuBminus, ite_eq_right hk.ne'] using hreg
    rw [bridge_Bminus x τ hk hr]
    exact prop_4_2_Bminus x τ hn hk hDelta

/-- Theorem A, equation (1.5), p.2; requires `k≥1`. -/
theorem theorem_A_1_5 (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaPlus x ≠ 0) (hreg : ExternalHL.Admissible x t (1)) :
    ExternalHL.Bplus x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hPlusKernel (classicalCoefficients x) i m) := by
  rw [bridge_Bplus x t hk hreg]
  exact prop_5_3_Bplus x t hn hk hDelta

/-- Theorem A, equation (1.6), p.2. -/
theorem theorem_A_1_6 (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x t (1)) :
    ExternalHL.C0 x t k = JK (k := k) (2*(k:ℤ)+2)
      (fun j y => t^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  by_cases hk0 : k = 0
  · subst k
    rw [prop_6_1_C0 x t hreg]
    simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [bridge_C0 x t hk hreg]
    exact prop_4_1_C0 x t hn hk hDelta

/-- Theorem A, equation (1.7), p.2. -/
theorem theorem_A_1_7 (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x t (ExternalHL.nuCt n k t)) :
    ExternalHL.Ct x t k = JKEven (k := k) (2*(k:ℤ))
      (fun j y => t^((k:ℤ)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  by_cases hk0 : k = 0
  · subst k
    rw [prop_6_1_Ct x t hreg]
    simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hr : ExternalHL.Admissible x t 1 := by
      simpa only [ExternalHL.nuCt, ite_eq_right hk.ne'] using hreg
    rw [bridge_Ct x t hk hr]
    exact prop_5_1_Ct x t hn hk hDelta

/-- Theorem A, equation (1.8), p.2. -/
theorem theorem_A_1_8 (x : Fin n → Fˣ) (τ : F) (hn : 0<n) (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x (τ^2) (1)) :
    ExternalHL.BC x τ k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:F)^y * τ^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients x) i m) := by
  by_cases hk0 : k = 0
  · subst k
    rw [prop_6_1_BC x τ hreg]
    simp
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [bridge_BC x τ hk hreg]
    exact prop_4_1_BC x τ hn hk hDelta

/-- Theorem B, equation (1.9), p.2. -/
theorem theorem_B_1_9 (x : Fin n → Fˣ) (t : F) (hn : 0<n) (hk : 0<k) (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x t (1)) :
    ExternalHL.Bt x t k = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hHatKernel (classicalCoefficients x) i m) := by
  rw [bridge_Bt x t hk hreg]
  exact prop_5_5_Bt x t hn hk hDelta

/-- The separate normalized endpoint in Theorem A, after (1.5). -/
theorem theorem_A_Bplus_width_zero (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (ExternalHL.nuBplus n 0 t)) :
    ExternalHL.Bplus x t 0 = 1 := prop_6_1_Bplus x t hreg

/-- The separate normalized endpoint in Theorem B, after (1.9). -/
theorem theorem_B_Bt_width_zero (x : Fin n → Fˣ) (t : F) (hreg : ExternalHL.Admissible x t (ExternalHL.nuCt n 0 t)) :
    ExternalHL.Bt x t 0 = 1 := prop_6_1_Bt x t hreg

end Main
end
end AffineDualJT
