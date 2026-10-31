import AffineDualJT.ClassicalColumns
import AffineDualJT.AdjacentColumns

/-! The adjacent-coefficient determinant identity in Corollary 6.2. -/

namespace AffineDualJT
open Matrix
noncomputable section

variable {F : Type*} [Field F] [CharZero F]
variable {n k : ℕ}

/-- The second equality in (6.2), from the adjacent-column transformation. -/
theorem classical_parity_minor_identity (x : Fin n → Fˣ) (_hn : 0 < n) (hk : 0 < k) :
    Matrix.det (fun i j => hKernel (classicalCoefficients x) i (paperIndex j) :
      Matrix (Fin k) (Fin k) F) =
      (2:F)⁻¹ * Matrix.det (fun i j => hHatKernel (classicalCoefficients x) i (paperIndex j) :
        Matrix (Fin k) (Fin k) F) := by
  rw [det_hHat_eq_two_det_h (classicalCoefficients x) hk]
  field_simp

end
end AffineDualJT
