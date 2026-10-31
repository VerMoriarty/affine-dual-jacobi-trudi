import AffineDualJT.HallLittlewoodFinite

/-!
# The seven Hall–Littlewood specializations in Corollary 6.2

These prove the corollary's final sentence for the actual Weyl-sum left
sides, rather than just identifying the seven column matrices at zero.
The characteristic-zero field interface retains the rational-expression
regularity conditions; `PaperSpecializations` discharges them in the paper's
field.
-/

namespace AffineDualJT
open Matrix
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

private theorem classical_PhiC_mul (x : Fin n → Fˣ) :
    (PhiC (k := k) x * classicalV : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiC (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp [lastRowsY, PhiC, transpose_apply, paperIndex, Nat.cast_add, add_assoc]

private theorem classical_PhiB_mul (x : Fin n → Fˣ) :
    (PhiB (k := k) x * classicalV : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiB (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp [lastRowsY, PhiB, transpose_apply, paperIndex, Nat.cast_add, add_assoc]

private theorem classical_PhiPlus_mul (x : Fin n → Fˣ) (hk : 0 < k) :
    (PhiPlus (k := k) x * classicalV : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => Cfun ((k : ℤ) + paperIndex r - 1) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiPlus (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp only [lastRowsY, PhiPlus, transpose_apply, paperIndex, Nat.cast_add]
  rw [ite_eq_right (by omega)]
  congr 1
  omega

/-- Corollary 6.2, `C0` specializes to the left side of (6.1). -/
theorem cor_6_2_C0_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.C0 x 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaC x := by
  rw [prop_2_2_C0_HL x 0 hn hk hDelta hreg, VC0_zero]
  exact congrArg (fun z : F => z / DeltaC x) (classical_PhiC_mul (k := k) x)

/-- Corollary 6.2, `Ct` specializes to the left side of (6.1). -/
theorem cor_6_2_Ct_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Ct x 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaC x := by
  rw [prop_2_2_Ct_HL x 0 hn hk hDelta hreg, VCt_zero]
  exact congrArg (fun z : F => z / DeltaC x) (classical_PhiC_mul (k := k) x)

/-- Corollary 6.2, `BC` uses `τ=0`. -/
theorem cor_6_2_BC_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.BC x 0 k =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaC x := by
  have hr : ExternalHL.Admissible x ((0 : F) ^ 2) 1 := by simpa using hreg
  rw [prop_2_2_BC_HL x 0 hn hk hDelta hr, VBC_zero]
  exact congrArg (fun z : F => z / DeltaC x) (classical_PhiC_mul (k := k) x)

/-- Corollary 6.2, `B0` specializes to the left side of (6.2). -/
theorem cor_6_2_B0_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.B0 x 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaB x := by
  rw [prop_2_2_B0_HL x 0 hn hk hDelta hreg, VB0_zero]
  exact congrArg (fun z : F => z / DeltaB x) (classical_PhiB_mul (k := k) x)

/-- Corollary 6.2, `Bminus` uses `τ=0`. -/
theorem cor_6_2_Bminus_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Bminus x 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaB x := by
  have hr : ExternalHL.Admissible x ((0 : F) ^ 2) 1 := by simpa using hreg
  rw [prop_2_2_Bminus_HL x 0 hn hk hDelta hr, VBminus_zero]
  exact congrArg (fun z : F => z / DeltaB x) (classical_PhiB_mul (k := k) x)

/-- Corollary 6.2, `Bt` specializes to the left side of (6.2). -/
theorem cor_6_2_Bt_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Bt x 0 k =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaB x := by
  rw [prop_2_2_Bt_HL x 0 hn hk hDelta hreg, VBt_zero]
  exact congrArg (fun z : F => z / DeltaB x) (classical_PhiB_mul (k := k) x)

/-- Corollary 6.2, `Bplus` specializes to the left side of (6.3). -/
theorem cor_6_2_Bplus_zero_HL [CharZero F] (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaPlus x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Bplus x 0 k =
      Matrix.det (Matrix.of fun a r => Cfun ((k : ℤ) + paperIndex r - 1) (x a : F) :
        Matrix (Fin n) (Fin n) F) / DeltaPlus x := by
  rw [prop_2_2_Bplus_HL x 0 hn hk hDelta hreg, VBplus_zero hk]
  exact congrArg (fun z : F => z / DeltaPlus x) (classical_PhiPlus_mul (k := k) x hk)

end
end AffineDualJT
