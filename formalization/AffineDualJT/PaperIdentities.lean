import AffineDualJT.MainIdentities
import AffineDualJT.PaperWeylRegularity

/-!
# Theorems A and B in the paper's symbolic rational function field

All regularity and denominator hypotheses of the general field interface
are discharged here using independence of the symbolic coordinates.
-/
namespace AffineDualJT
open AffineDetSum
noncomputable section
variable {n k : ℕ}

/-- theorem_A_1_3 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_3 (hn : 0<n) :
    ExternalHL.B0 (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (fun i m => hKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_3 (paperVariables n) (paperParameter n) hn (paper_DeltaB_ne_zero n) (paper_admissible n)

/-- theorem_A_1_4 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_4 (hn : 0<n) :
    ExternalHL.Bminus (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ))
      (fun j y => (paperParameter n)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (fun i m => hKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_4 (paperVariables n) (paperParameter n) hn (paper_DeltaB_ne_zero n) (paper_admissible_Bminus n k)

/-- theorem_A_1_5 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_5 (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bplus (paperVariables n) (paperParameter n) k = (2:PaperField n)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hPlusKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_5 (paperVariables n) (paperParameter n) hn hk (paper_DeltaPlus_ne_zero n) (paper_admissible n)

/-- theorem_A_1_6 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_6 (hn : 0<n) :
    ExternalHL.C0 (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+2)
      (fun j y => (paperParameter n)^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_6 (paperVariables n) (paperParameter n) hn (paper_DeltaC_ne_zero n) (paper_admissible n)

/-- theorem_A_1_7 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_7 (hn : 0<n) :
    ExternalHL.Ct (paperVariables n) (paperParameter n) k = JKEven (k := k) (2*(k:ℤ))
      (fun j y => (paperParameter n)^((k:ℤ)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_7 (paperVariables n) (paperParameter n) hn (paper_DeltaC_ne_zero n) (paper_admissible_Ct n k)

/-- theorem_A_1_8 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_1_8 (hn : 0<n) :
    ExternalHL.BC (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_A_1_8 (paperVariables n) (paperParameter n) hn (paper_DeltaC_ne_zero n) (paper_admissible_squared n)

/-- theorem_B_1_9 over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_B_1_9 (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bt (paperVariables n) (paperParameter n) k = (2:PaperField n)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hHatKernel (classicalCoefficients (paperVariables n)) i m) :=
  theorem_B_1_9 (paperVariables n) (paperParameter n) hn hk (paper_DeltaB_ne_zero n) (paper_admissible n)

/-- theorem_A_Bplus_width_zero over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_A_Bplus_width_zero :
    ExternalHL.Bplus (paperVariables n) (paperParameter n) 0 = 1 :=
  theorem_A_Bplus_width_zero (paperVariables n) (paperParameter n) (paper_admissible_Bplus n 0)

/-- theorem_B_Bt_width_zero over `ℚ(t,x₁,…,xₙ)` (or the square-root parameter `τ`). -/
theorem paper_theorem_B_Bt_width_zero :
    ExternalHL.Bt (paperVariables n) (paperParameter n) 0 = 1 :=
  theorem_B_Bt_width_zero (paperVariables n) (paperParameter n) (paper_admissible_Ct n 0)

end
end AffineDualJT
