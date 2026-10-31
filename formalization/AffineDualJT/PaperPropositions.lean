import AffineDualJT.HallLittlewoodFinite
import AffineDualJT.HallLittlewoodAffine
import AffineDualJT.PaperWeylRegularity
import AffineDualJT.ExceptionalSequences

/-!
# Positive-width propositions in the exact symbolic domain of source.tex

Each wrapper has only the paper's `n≥1` and `k≥1` hypotheses. The extra
denominator and regularity hypotheses of the general-field interfaces are
proved, rather than added to the paper statements.
-/

namespace AffineDualJT
open AffineDetSum
noncomputable section
variable {n k : ℕ}

/-- Lemma 5.2 in the paper's symbolic parameter field. -/
theorem paper_lemma_5_2_quasiperiod (j : Fin k) (m : ℤ) :
    bBplus (paperParameter n) j (m+2*(k:ℤ)) =
      -(paperParameter n)^(m+(k:ℤ)-1) * bBplus (paperParameter n) j m :=
  lemma_5_2_quasiperiod (paperParameter n) (paperParameter_ne_zero n) j m

theorem paper_lemma_5_2_center (j : Fin k) (m : ℤ) :
    Gamma (paperParameter n) j (2-m) = Gamma (paperParameter n) j m :=
  lemma_5_2_center (paperParameter n) j m

theorem paper_lemma_5_2_affine (j : Fin k) (m : ℤ) :
    Gamma (paperParameter n) j m =
      -(paperParameter n)^(m-(k:ℤ)-1) * Gamma (paperParameter n) j (2*(k:ℤ)+2-m) :=
  lemma_5_2_affine (paperParameter n) (paperParameter_ne_zero n) j m

theorem paper_lemma_5_2_fixed (j : Fin k) :
    Gamma (paperParameter n) j ((k:ℤ)+1) = 0 :=
  lemma_5_2_fixed (paperParameter n) (paperParameter_ne_zero n) j

/-- Lemma 5.4 in the paper's symbolic parameter field. -/
theorem paper_lemma_5_4_eq_5_3 (j : Fin k) (m : ℤ) :
    cBt (paperParameter n) j m = Gamma (paperParameter n) j m - Gamma (paperParameter n) j (m+1) :=
  lemma_5_4_eq_5_3 (paperParameter n) j m

theorem paper_lemma_5_4_eq_5_4 (j : Fin k) (m : ℤ) :
    gammaBt (paperParameter n) j m = (1+paperParameter n)*Gamma (paperParameter n) j m -
      Gamma (paperParameter n) j (m+1) - paperParameter n*Gamma (paperParameter n) j (m-1) :=
  lemma_5_4_eq_5_4 (paperParameter n) j m

theorem paper_lemma_5_4_eq_5_5 (j : Fin k) (m : ℤ) :
    gammaBt (paperParameter n) j m =
      -(paperParameter n)^(m-(k:ℤ)-1) * gammaBt (paperParameter n) j (2*(k:ℤ)+2-m) :=
  lemma_5_4_eq_5_5 (paperParameter n) (paperParameter_ne_zero n) j m

theorem paper_lemma_5_4_fixed (j : Fin k) :
    gammaBt (paperParameter n) j ((k:ℤ)+1) = 0 :=
  lemma_5_4_fixed (paperParameter n) (paperParameter_ne_zero n) j

/-- Proposition 2.2, C0, over the paper's rational function field. -/
theorem paper_prop_2_2_C0 (hn : 0<n) (hk : 0<k) :
    ExternalHL.C0 (paperVariables n) (paperParameter n) k =
      (PhiC (k := k) (paperVariables n)*VC0 (n := n) (k := k) (paperParameter n)).det/DeltaC (paperVariables n) :=
  prop_2_2_C0_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible n)

/-- Proposition 2.2, Ct, over the paper's rational function field. -/
theorem paper_prop_2_2_Ct (hn : 0<n) (hk : 0<k) :
    ExternalHL.Ct (paperVariables n) (paperParameter n) k =
      (PhiC (k := k) (paperVariables n)*VCt (n := n) (k := k) (paperParameter n)).det/DeltaC (paperVariables n) :=
  prop_2_2_Ct_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible n)

/-- Proposition 2.2, BC, over the paper's rational function field. -/
theorem paper_prop_2_2_BC (hn : 0<n) (hk : 0<k) :
    ExternalHL.BC (paperVariables n) (paperParameter n) k =
      (PhiC (k := k) (paperVariables n)*VBC (n := n) (k := k) (paperParameter n)).det/DeltaC (paperVariables n) :=
  prop_2_2_BC_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible_squared n)

/-- Proposition 2.2, B0, over the paper's rational function field. -/
theorem paper_prop_2_2_B0 (hn : 0<n) (hk : 0<k) :
    ExternalHL.B0 (paperVariables n) (paperParameter n) k =
      (PhiB (k := k) (paperVariables n)*VB0 (n := n) (k := k) (paperParameter n)).det/DeltaB (paperVariables n) :=
  prop_2_2_B0_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible n)

/-- Proposition 2.2, Bminus, over the paper's rational function field. -/
theorem paper_prop_2_2_Bminus (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bminus (paperVariables n) (paperParameter n) k =
      (PhiB (k := k) (paperVariables n)*VBminus (n := n) (k := k) (paperParameter n)).det/DeltaB (paperVariables n) :=
  prop_2_2_Bminus_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible_squared n)

/-- Proposition 2.2, Bplus, over the paper's rational function field. -/
theorem paper_prop_2_2_Bplus (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bplus (paperVariables n) (paperParameter n) k =
      (PhiPlus (k := k) (paperVariables n)*VBplus (n := n) (k := k) (paperParameter n)).det/DeltaPlus (paperVariables n) :=
  prop_2_2_Bplus_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaPlus_ne_zero n) (paper_admissible n)

/-- Proposition 2.2, Bt, over the paper's rational function field. -/
theorem paper_prop_2_2_Bt (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bt (paperVariables n) (paperParameter n) k =
      (PhiB (k := k) (paperVariables n)*VBt (n := n) (k := k) (paperParameter n)).det/DeltaB (paperVariables n) :=
  prop_2_2_Bt_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible n)

/-- Proposition 4.1, case C0, in the paper's symbolic domain. -/
theorem paper_prop_4_1_C0 (hn : 0<n) (hk : 0<k) :
    ExternalHL.C0 (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+2)
      (fun j y => (paperParameter n)^(((k:ℤ)+1)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_4_1_C0_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible n)

/-- Proposition 4.1, case BC, in the paper's symbolic domain. -/
theorem paper_prop_4_1_BC (hn : 0<n) (hk : 0<k) :
    ExternalHL.BC (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((2*(k:ℤ)+1)*y^2-2*paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_4_1_BC_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible_squared n)

/-- Proposition 4.2, case B0, in the paper's symbolic domain. -/
theorem paper_prop_4_2_B0 (hn : 0<n) (hk : 0<k) :
    ExternalHL.B0 (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ)+1)
      (fun j y => (-1:PaperField n)^y *
        (paperParameter n)^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
      (fun i m => hKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_4_2_B0_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible n)

/-- Proposition 4.2, case Bminus, in the paper's symbolic domain. -/
theorem paper_prop_4_2_Bminus (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bminus (paperVariables n) (paperParameter n) k = JK (k := k) (2*(k:ℤ))
      (fun j y => (paperParameter n)^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
      (fun i m => hKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_4_2_Bminus_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible_squared n)

/-- Proposition 5.1, case Ct, in the paper's symbolic domain. -/
theorem paper_prop_5_1_Ct (hn : 0<n) (hk : 0<k) :
    ExternalHL.Ct (paperVariables n) (paperParameter n) k = JKEven (k := k) (2*(k:ℤ))
      (fun j y => (paperParameter n)^((k:ℤ)*y^2-paperIndex j*y))
      (fun i m => lambdaKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_5_1_Ct_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible n)

/-- Proposition 5.3, case Bplus, in the paper's symbolic domain. -/
theorem paper_prop_5_3_Bplus (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bplus (paperVariables n) (paperParameter n) k = (2 : PaperField n)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hPlusKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_5_3_Bplus_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaPlus_ne_zero n) (paper_admissible n)

/-- Proposition 5.5, case Bt, in the paper's symbolic domain. -/
theorem paper_prop_5_5_Bt (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bt (paperVariables n) (paperParameter n) k = (2 : PaperField n)⁻¹ * JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:PaperField n)^y * (paperParameter n)^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (fun i m => hHatKernel (classicalCoefficients (paperVariables n)) i m) :=
  prop_5_5_Bt_HL (paperVariables n) (paperParameter n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible n)

end
end AffineDualJT
