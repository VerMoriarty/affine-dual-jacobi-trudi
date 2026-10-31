import AffineDualJT.PaperIdentities
import AffineDualJT.HallLittlewoodClassical
import AffineDualJT.ClassicalCorollary

/-!
# Propositions 6.1 and Corollary 6.2 in the paper's symbolic domain

The zero-parameter identities use the original Weyl definitions at `t=0`
(or `τ=0`). This is direct specialization with a nonzero normalization;
the symbolic-domain statements do not assert values at singular inputs.
-/

namespace AffineDualJT
open Matrix
open scoped BigOperators
noncomputable section
variable {n k : ℕ}

/-- Independence of the `x` variables also gives regularity at parameter zero. -/
theorem paper_admissible_zero (n : ℕ) :
    ExternalHL.Admissible (paperVariables n) 0 1 := by
  apply paper_admissible_of_normalization
  have hV : ExternalHL.Vn n (0 : PaperField n) = 1 := by
    unfold ExternalHL.Vn
    have hsum (r : Fin n) :
        (∑ l ∈ Finset.range (r.val + 1), (0 : PaperField n) ^ l) = 1 := by
      rw [Finset.sum_range_succ']
      simp
    simp_rw [hsum]
    simp
  rw [hV, one_mul]
  exact one_ne_zero

/-- Proposition 6.1, normalized empty rectangle C0. -/
theorem paper_prop_6_1_C0 (_hn : 0<n) :
    ExternalHL.C0 (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_C0 (paperVariables n) (paperParameter n) (paper_admissible n)

/-- Proposition 6.1, normalized empty rectangle Ct. -/
theorem paper_prop_6_1_Ct (_hn : 0<n) :
    ExternalHL.Ct (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_Ct (paperVariables n) (paperParameter n) (paper_admissible_Ct n 0)

/-- Proposition 6.1, normalized empty rectangle BC. -/
theorem paper_prop_6_1_BC (_hn : 0<n) :
    ExternalHL.BC (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_BC (paperVariables n) (paperParameter n) (paper_admissible_squared n)

/-- Proposition 6.1, normalized empty rectangle B0. -/
theorem paper_prop_6_1_B0 (_hn : 0<n) :
    ExternalHL.B0 (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_B0 (paperVariables n) (paperParameter n) (paper_admissible n)

/-- Proposition 6.1, normalized empty rectangle Bminus. -/
theorem paper_prop_6_1_Bminus (_hn : 0<n) :
    ExternalHL.Bminus (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_Bminus (paperVariables n) (paperParameter n) (paper_admissible_Bminus n 0)

/-- Proposition 6.1, normalized empty rectangle Bplus. -/
theorem paper_prop_6_1_Bplus (_hn : 0<n) :
    ExternalHL.Bplus (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_Bplus (paperVariables n) (paperParameter n) (paper_admissible_Bplus n 0)

/-- Proposition 6.1, normalized empty rectangle Bt. -/
theorem paper_prop_6_1_Bt (_hn : 0<n) :
    ExternalHL.Bt (paperVariables n) (paperParameter n) 0 = 1 :=
  prop_6_1_Bt (paperVariables n) (paperParameter n) (paper_admissible_Ct n 0)

/-- Corollary 6.2, equality 6_1, with no extra denominator hypothesis. -/
theorem paper_cor_6_2_eq_6_1 (hn : 0<n) (hk : 0<k) :
    Matrix.det (Matrix.of fun a r => phi ((k:ℤ)+paperIndex r) ((paperVariables n) a : PaperField n) : Matrix (Fin n) (Fin n) (PaperField n)) / DeltaC (paperVariables n) =
      Matrix.det (fun i j => lambdaKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
        Matrix (Fin k) (Fin k) (PaperField n)) :=
  cor_6_2_eq_6_1 (paperVariables n) hn hk (paper_DeltaC_ne_zero n)

/-- Corollary 6.2, equality 6_2a, with no extra denominator hypothesis. -/
theorem paper_cor_6_2_eq_6_2a (hn : 0<n) (hk : 0<k) :
    Matrix.det (Matrix.of fun a r => psi ((k:ℤ)+paperIndex r) ((paperVariables n) a : PaperField n) : Matrix (Fin n) (Fin n) (PaperField n)) / DeltaB (paperVariables n) =
      Matrix.det (fun i j => hKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
        Matrix (Fin k) (Fin k) (PaperField n)) :=
  cor_6_2_eq_6_2a (paperVariables n) hn hk (paper_DeltaB_ne_zero n)

/-- Corollary 6.2, equality 6_2b, with no extra denominator hypothesis. -/
theorem paper_cor_6_2_eq_6_2b (hn : 0<n) (hk : 0<k) :
    Matrix.det (fun i j => hKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
      Matrix (Fin k) (Fin k) (PaperField n)) =
      (2 : PaperField n)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
        Matrix (Fin k) (Fin k) (PaperField n)) :=
  cor_6_2_eq_6_2b (paperVariables n) hn hk (paper_DeltaB_ne_zero n)

/-- Corollary 6.2, equality 6_2b_ratio, with no extra denominator hypothesis. -/
theorem paper_cor_6_2_eq_6_2b_ratio (hn : 0<n) (hk : 0<k) :
    Matrix.det (Matrix.of fun a r => psi ((k:ℤ)+paperIndex r) ((paperVariables n) a : PaperField n) : Matrix (Fin n) (Fin n) (PaperField n)) / DeltaB (paperVariables n) =
      (2 : PaperField n)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
        Matrix (Fin k) (Fin k) (PaperField n)) :=
  cor_6_2_eq_6_2b_ratio (paperVariables n) hn hk (paper_DeltaB_ne_zero n)

/-- Corollary 6.2, equality 6_3, with no extra denominator hypothesis. -/
theorem paper_cor_6_2_eq_6_3 (hn : 0<n) (hk : 0<k) :
    Matrix.det (Matrix.of fun a r => Cfun ((k:ℤ)+paperIndex r-1) ((paperVariables n) a : PaperField n) : Matrix (Fin n) (Fin n) (PaperField n)) / DeltaPlus (paperVariables n) =
      (2 : PaperField n)⁻¹ *
      Matrix.det (fun i j => hPlusKernel (classicalCoefficients (paperVariables n)) i (paperIndex j) :
        Matrix (Fin k) (Fin k) (PaperField n)) :=
  cor_6_2_eq_6_3 (paperVariables n) hn hk (paper_DeltaPlus_ne_zero n)

/-- Corollary 6.2, final sentence, C0 at zero parameter. -/
theorem paper_cor_6_2_C0_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.C0 (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaC (paperVariables n) :=
  calc
    ExternalHL.C0 (paperVariables n) 0 k = RedC0 (paperVariables n) 0 k :=
      bridge_C0 (paperVariables n) 0 hk (paper_admissible_zero n)
    _ = _ := cor_6_2_C0_zero_quotient (paperVariables n) hn hk (paper_DeltaC_ne_zero n)

/-- Corollary 6.2, final sentence, Ct at zero parameter. -/
theorem paper_cor_6_2_Ct_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.Ct (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaC (paperVariables n) :=
  cor_6_2_Ct_zero_via_parity (paperVariables n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible_zero n)

/-- Corollary 6.2, final sentence, BC at zero parameter. -/
theorem paper_cor_6_2_BC_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.BC (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaC (paperVariables n) :=
  cor_6_2_BC_zero_HL (paperVariables n) hn hk
    (paper_DeltaC_ne_zero n) (paper_admissible_zero n)

/-- Corollary 6.2, final sentence, B0 at zero parameter. -/
theorem paper_cor_6_2_B0_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.B0 (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaB (paperVariables n) :=
  calc
    ExternalHL.B0 (paperVariables n) 0 k = RedB0 (paperVariables n) 0 k :=
      bridge_B0 (paperVariables n) 0 hk (paper_admissible_zero n)
    _ = _ := cor_6_2_B0_zero_quotient (paperVariables n) hn hk (paper_DeltaB_ne_zero n)

/-- Corollary 6.2, final sentence, Bminus at zero parameter. -/
theorem paper_cor_6_2_Bminus_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bminus (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaB (paperVariables n) :=
  cor_6_2_Bminus_zero_HL (paperVariables n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible_zero n)

/-- Corollary 6.2, final sentence, Bt at zero parameter. -/
theorem paper_cor_6_2_Bt_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bt (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaB (paperVariables n) :=
  (cor_6_2_Bt_zero_affine (paperVariables n) hn hk
    (paper_DeltaB_ne_zero n) (paper_admissible_zero n)).trans
    (cor_6_2_eq_6_2b_ratio (paperVariables n) hn hk (paper_DeltaB_ne_zero n)).symm

/-- Corollary 6.2, final sentence, Bplus at zero parameter. -/
theorem paper_cor_6_2_Bplus_zero (hn : 0<n) (hk : 0<k) :
    ExternalHL.Bplus (paperVariables n) 0 k =
      Matrix.det (Matrix.of fun a r => Cfun ((k : ℤ) + paperIndex r - 1) ((paperVariables n) a : PaperField n) :
        Matrix (Fin n) (Fin n) (PaperField n)) / DeltaPlus (paperVariables n) :=
  calc
    ExternalHL.Bplus (paperVariables n) 0 k = RedBplus (paperVariables n) 0 k :=
      bridge_Bplus (paperVariables n) 0 hk (paper_admissible_zero n)
    _ = _ := cor_6_2_Bplus_zero_quotient (paperVariables n) hn hk (paper_DeltaPlus_ne_zero n)

end
end AffineDualJT
