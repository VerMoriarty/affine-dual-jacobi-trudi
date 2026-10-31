import AffineDualJT.MainIdentities
import AffineDualJT.Section5Exceptional
import AffineDualJT.ClassicalColumns
import AffineDualJT.ClassicalSpecialization

/-!
# Corollary 6.2: specialize the affine sums at parameter zero

The proofs first specialize the Table 1 finite columns, then use the §4--5
identities. For `C0`, `B0`, `B+`, and `Bt`, strict positivity of every
nonzero-shift exponent leaves only `y=0`. The `Ct` endpoint is recorded
separately because its boundary shift survives and must pass through the even-
lattice parity projector.
-/
namespace AffineDualJT
open Matrix AffineDetSum
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable {n k : ℕ}

omit [CharZero F] in
private theorem classical_PhiC_mul (x : Fin n → Fˣ) :
    (PhiC (k := k) x * classicalV (n := n) (k := k) : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => phi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiC (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp [lastRowsY, PhiC, transpose_apply, paperIndex, Nat.cast_add, add_assoc]

omit [CharZero F] in
private theorem classical_PhiB_mul (x : Fin n → Fˣ) :
    (PhiB (k := k) x * classicalV (n := n) (k := k) : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => psi ((k : ℤ) + paperIndex r) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiB (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp [lastRowsY, PhiB, transpose_apply, paperIndex, Nat.cast_add, add_assoc]

omit [CharZero F] in
private theorem classical_PhiPlus_mul (x : Fin n → Fˣ) (hk : 0 < k) :
    (PhiPlus (k := k) x * classicalV (n := n) (k := k) : Matrix (Fin n) (Fin n) F).det =
      Matrix.det (Matrix.of fun a r => Cfun ((k : ℤ) + paperIndex r - 1) (x a : F) :
        Matrix (Fin n) (Fin n) F) := by
  refine (congrArg Matrix.det (classical_phi_mul (PhiPlus (k := k) x))).trans ?_
  apply congrArg Matrix.det
  ext a r
  simp only [lastRowsY, PhiPlus, transpose_apply, paperIndex, Nat.cast_add]
  rw [ite_eq_right (by omega)]
  congr 1
  omega

omit [CharZero F] in
/-- At zero parameter the C finite quotient is `RedC0`. -/
theorem cor_6_2_C0_zero_quotient (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) :
    RedC0 x 0 k =
      Matrix.det (fun a r => phi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaC x := by
  have h := prop_2_2_C0 x 0 hn hk hDelta
  rw [VC0_zero] at h
  exact h.trans (congrArg (fun z : F => z / DeltaC x) (classical_PhiC_mul x))

theorem cor_6_2_eq_6_1 (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) :
    Matrix.det (fun a r => phi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaC x =
      Matrix.det (fun i j => lambdaKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  have hfinite := cor_6_2_C0_zero_quotient x hn hk hDelta
  have hsum := prop_4_1_C0 x 0 hn hk hDelta
  have hzero :
      JK (k := k) (2*(k:ℤ)+2) (fun j y => (0:F)^(((k:ℤ)+1)*y^2-paperIndex j*y))
        (lambdaKernel (classicalCoefficients x)) =
      Matrix.det (fun i j => lambdaKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
    symm
    apply JK_of_zero_shifts _ (by omega) _ _ (lambdaKernel_hasFiniteSupport _)
    · intro j
      simp
    · exact C0_weight_zero
  calc
    _ = RedC0 x 0 k := hfinite.symm
    _ = JK (k := k) (2*(k:ℤ)+2)
        (fun j y => (0:F)^(((k:ℤ)+1)*y^2-paperIndex j*y))
        (lambdaKernel (classicalCoefficients x)) := hsum
    _ = _ := hzero

omit [CharZero F] in
/-- At zero parameter the B0 finite quotient is `RedB0`. -/
theorem cor_6_2_B0_zero_quotient (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) :
    RedB0 x 0 k =
      Matrix.det (fun a r => psi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaB x := by
  have h := prop_2_2_B0 x 0 hn hk hDelta
  rw [VB0_zero] at h
  exact h.trans (congrArg (fun z : F => z / DeltaB x) (classical_PhiB_mul x))

theorem cor_6_2_eq_6_2a (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) :
    Matrix.det (fun a r => psi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaB x =
      Matrix.det (fun i j => hKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  have hfinite := cor_6_2_B0_zero_quotient x hn hk hDelta
  have hsum := prop_4_2_B0 x 0 hn hk hDelta
  have hzero :
      JK (k := k) (2*(k:ℤ)+1)
        (fun j y => (-1:F)^y * (0:F)^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
        (hKernel (classicalCoefficients x)) =
      Matrix.det (fun i j => hKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
    symm
    apply JK_of_zero_shifts _ (by omega) _ _ (hKernel_hasFiniteSupport _)
    · intro j
      simp
    · intro j y hy
      rw [B0_weight_zero j y hy, mul_zero]
  calc
    _ = RedB0 x 0 k := hfinite.symm
    _ = JK (k := k) (2*(k:ℤ)+1)
        (fun j y => (-1:F)^y * (0:F)^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
        (hKernel (classicalCoefficients x)) := hsum
    _ = _ := hzero

/-- The Bt affine identity at zero gives the second determinant in (6.2). -/
theorem cor_6_2_eq_6_2b_ratio (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) :
    Matrix.det (fun a r => psi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaB x =
      (2:F)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  have hfinite := prop_2_2_Bt x 0 hn hk hDelta
  rw [VBt_zero] at hfinite
  have hquot : RedBt x 0 k =
      Matrix.det (fun a r => psi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaB x :=
    hfinite.trans (congrArg (fun z : F => z / DeltaB x) (classical_PhiB_mul x))
  have hsum := prop_5_5_Bt x 0 hn hk hDelta
  have hzero : JK (k := k) (2*(k:ℤ))
      (fun j y => (-1:F)^y * (0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y))
      (hHatKernel (classicalCoefficients x)) =
      Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
    symm
    apply JK_of_zero_shifts _ (by omega) _ _ (hHatKernel_hasFiniteSupport _)
    · intro j
      simp
    · intro j y hy
      rw [Bt_weight_zero j y hy, mul_zero]
  exact hquot.symm.trans (hsum.trans (congrArg (fun z : F => (2:F)⁻¹ * z) hzero))

/-- The two zero-parameter affine identities have the same finite quotient. -/
theorem cor_6_2_eq_6_2b (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) :
    Matrix.det (fun i j => hKernel (classicalCoefficients x) i (paperIndex j) :
      Matrix (Fin k) (Fin k) F) =
      (2:F)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) :=
  (cor_6_2_eq_6_2a x hn hk hDelta).symm.trans (cor_6_2_eq_6_2b_ratio x hn hk hDelta)

omit [CharZero F] in
/-- At zero parameter the B+ finite quotient is `RedBplus`. -/
theorem cor_6_2_Bplus_zero_quotient (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaPlus x ≠ 0) :
    RedBplus x 0 k =
      Matrix.det (fun a r => Cfun ((k:ℤ)+paperIndex r-1) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaPlus x := by
  have h := prop_2_2_Bplus x 0 hn hk hDelta
  rw [VBplus_zero hk] at h
  exact h.trans (congrArg (fun z : F => z / DeltaPlus x) (classical_PhiPlus_mul x hk))

theorem cor_6_2_eq_6_3 (x : Fin n → Fˣ) (_hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaPlus x ≠ 0) :
    Matrix.det (fun a r => Cfun ((k:ℤ)+paperIndex r-1) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaPlus x =
      (2:F)⁻¹ * Matrix.det (fun i j => hPlusKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  have hfinite := cor_6_2_Bplus_zero_quotient x _hn hk hDelta
  have hsum := prop_5_3_Bplus x 0 _hn hk hDelta
  have hzero :
      (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
        (fun j y => (-1:F)^y * (0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y))
        (hPlusKernel (classicalCoefficients x)) =
      (2:F)⁻¹ * Matrix.det (fun i j => hPlusKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
    apply congrArg (fun z : F => (2:F)⁻¹*z)
    symm
    apply JK_of_zero_shifts _ (by omega) _ _ (hPlusKernel_hasFiniteSupport _)
    · intro j
      simp
    · intro j y hy
      rw [Bplus_weight_zero j y hy, mul_zero]
  calc
    _ = RedBplus x 0 k := hfinite.symm
    _ = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
        (fun j y => (-1:F)^y * (0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y))
        (hPlusKernel (classicalCoefficients x)) := hsum
    _ = _ := hzero

/-- For Ct, `j=k,y=1` has exponent zero.  The even-lattice parity projector
therefore supplies the bridge, while the finite-column specialization gives
exactly the same reduced quotient as C0. -/
theorem cor_6_2_Ct_zero_parity_bridge (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) :
    JKEven (k := k) (2*(k:ℤ)) (fun j y => (0:F)^((k:ℤ)*y^2-paperIndex j*y))
      (lambdaKernel (classicalCoefficients x)) = RedC0 x 0 k := by
  have hproject := Ct_even_sum_zero_parity (F := F) x hk
  have htransfer := exceptional_Ct_signed_identity x 0 hn hk hDelta
  have hct : RedCt x 0 k = RedC0 x 0 k := by
    have h1 := prop_2_2_Ct x 0 hn hk hDelta
    have h0 := prop_2_2_C0 x 0 hn hk hDelta
    rw [VCt_zero] at h1
    rw [VC0_zero] at h0
    exact h1.trans h0.symm
  calc
    _ = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
        (fun j y => (-1:F)^y * (0:F)^((k:ℤ)*y^2-paperIndex j*y))
        (lambdaKernel (classicalCoefficients x)) := hproject
    _ = RedCt x 0 k := htransfer.symm
    _ = _ := hct

/-- The Ct Weyl specialization follows the finite-column quotient and the
even-lattice parity bridge, including its surviving boundary shift. -/
theorem cor_6_2_Ct_zero_via_parity (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaC x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Ct x 0 k =
      Matrix.det (fun a r => phi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaC x := by
  have hbridge := bridge_Ct x 0 hk hreg
  have hprop := prop_5_1_Ct x 0 hn hk hDelta
  have hparity := cor_6_2_Ct_zero_parity_bridge x hn hk hDelta
  have hfinite : RedC0 x 0 k =
      Matrix.det (fun a r => phi ((k:ℤ)+paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F) / DeltaC x := by
    have h := prop_2_2_C0 x 0 hn hk hDelta
    rw [VC0_zero] at h
    exact h.trans (congrArg (fun z : F => z / DeltaC x) (classical_PhiC_mul x))
  calc
    ExternalHL.Ct x 0 k = RedCt x 0 k := hbridge
    _ = JKEven (k := k) (2*(k:ℤ)) (fun j y => (0:F)^((k:ℤ)*y^2-paperIndex j*y))
        (lambdaKernel (classicalCoefficients x)) := hprop
    _ = RedC0 x 0 k := hparity
    _ = _ := hfinite

/-- The Bt endpoint is obtained from Proposition 5.5's affine sum.  The Bt
exponent is strictly positive for every nonzero shift, so only `y=0` remains. -/
theorem cor_6_2_Bt_zero_affine (x : Fin n → Fˣ) (hn : 0 < n) (hk : 0 < k)
    (hDelta : DeltaB x ≠ 0) (hreg : ExternalHL.Admissible x 0 1) :
    ExternalHL.Bt x 0 k =
      (2:F)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  have hbridge := bridge_Bt x 0 hk hreg
  have hsum := prop_5_5_Bt x 0 hn hk hDelta
  have hzero :
      JK (k := k) (2*(k:ℤ))
        (fun j y => (-1:F)^y*(0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y))
        (hHatKernel (classicalCoefficients x)) =
      Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
    symm
    apply JK_of_zero_shifts _ (by omega) _ _ (hHatKernel_hasFiniteSupport _)
    · intro j
      simp
    · intro j y hy
      rw [Bt_weight_zero j y hy, mul_zero]
  calc
    ExternalHL.Bt x 0 k = RedBt x 0 k := hbridge
    _ = (2:F)⁻¹ * JK (k := k) (2*(k:ℤ))
        (fun j y => (-1:F)^y*(0:F)^((k:ℤ)*y^2-(paperIndex j-1)*y))
        (hHatKernel (classicalCoefficients x)) := hsum
    _ = _ := congrArg (fun z : F => (2:F)⁻¹*z) hzero

end
end AffineDualJT
