import AffineDualJT.Kernels

/-! Coordinate columns and their sign product for the finite specializations. -/
open Matrix
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

def classicalV : Matrix (Fin (n+k)) (Fin n) F :=
  (1 : Matrix (Fin (n+k)) (Fin (n+k)) F).submatrix id
    (fun r => ⟨k+r.val, by omega⟩)

theorem classical_phi_mul (Phi : Matrix (Fin n) (Fin (n+k)) F) :
    Phi * classicalV (F:=F) (n:=n) (k:=k) = (lastRowsY Phi.transpose).transpose := by
  exact mul_submatrix_one (Equiv.refl (Fin (n+k)))
      (fun r : Fin n => (⟨k+r.val, by omega⟩ : Fin (n+k))) Phi

theorem prod_first_sign : (∏ j : Fin k, (-1:F)^(j.val+1)) = omegaSign F k := by
  simpa [zetaSign] using prod_tail_rowSign (F:=F) (n:=0) (k:=k)
end
end AffineDualJT
