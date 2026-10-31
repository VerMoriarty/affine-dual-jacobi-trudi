import AffineDualJT.Basic

/-!
# The adjacent-coefficient column transform in Corollary 6.2

`hHat(j)=h(j)+h(j-1)`. At the first column, reflection identifies
`h(0)=h(1)`, so the column transform is upper bidiagonal with diagonal
`2,1,…,1`. This explains the half determinant involving `ddot e`.
-/
open Matrix
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
def adjacentColumnTransform : Matrix (Fin k) (Fin k) F :=
  Matrix.diagonal (fun j => if j.val = 0 then 2 else 1) +
    Matrix.of (fun r j => if r.val+1 = j.val then 1 else 0)

theorem adjacentColumnTransform_det (hk : 0 < k) :
    (adjacentColumnTransform (F:=F) (k:=k)).det = 2 := by
  rw [det_of_isUpperTriangular]
  · have hd : ∀ j : Fin k, adjacentColumnTransform (F:=F) j j = if j.val = 0 then 2 else 1 := by
      intro j
      simp [adjacentColumnTransform]
    simp_rw [hd]
    have he : ∀ j : Fin k, j.val = 0 ↔ j = ⟨0,hk⟩ := by
      intro j
      exact (Fin.ext_iff (a:=j) (b:=⟨0,hk⟩)).symm
    simp_rw [he]
    simp
  · intro r j h
    simp only [id_eq, Fin.lt_def] at h
    simp [adjacentColumnTransform, Matrix.diagonal, show r ≠ j by intro he; subst j; omega,
      show ¬r.val+1=j.val by omega]

theorem hHatMatrix_eq_mul (c : CoeffSystem F n) :
    Matrix.of (fun i j : Fin k => hHatKernel c i (paperIndex j)) =
      Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j)) * adjacentColumnTransform := by
  rw [adjacentColumnTransform, mul_add]
  ext i j
  change hHatKernel c i (paperIndex j) =
    (Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j)) *
      Matrix.diagonal (fun j : Fin k => if j.val = 0 then (2:F) else 1)) i j +
    (Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j)) *
      Matrix.of (fun r j : Fin k => if r.val+1=j.val then (1:F) else 0)) i j
  rw [mul_diagonal]
  simp only [of_apply, hHat_eq_h_add_shift]
  by_cases hz : j.val = 0
  · have hfirst : hKernel c i 0 = hKernel c i 1 := by
      simpa using hKernel_reflect c i 1
    have hshift : (Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j)) *
        Matrix.of (fun r j : Fin k => if r.val+1=j.val then (1:F) else 0)) i j = 0 := by
      rw [mul_apply]
      apply Finset.sum_eq_zero
      intro r hr
      simp [hz]
    rw [hshift]
    simp [paperIndex, hz, hfirst]
    ring
  · let prev : Fin k := ⟨j.val-1, by omega⟩
    have he : ∀ r : Fin k, r.val+1=j.val ↔ r=prev := by
      intro r
      rw [Fin.ext_iff]
      dsimp [prev]
      omega
    have hshift : (Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j)) *
        Matrix.of (fun r j : Fin k => if r.val+1=j.val then (1:F) else 0)) i j =
          hKernel c i (paperIndex prev) := by
      simp only [mul_apply, of_apply]
      simp_rw [he]
      simp
    rw [hshift]
    simp only [hz, ite_false, mul_one]
    congr 1
    congr 1
    simp only [paperIndex, prev]
    omega

theorem det_hHat_eq_two_det_h (c : CoeffSystem F n) (hk : 0 < k) :
    Matrix.det (fun i j => hHatKernel c i (paperIndex j) : Matrix (Fin k) (Fin k) F) =
      2 * Matrix.det (fun i j => hKernel c i (paperIndex j) : Matrix (Fin k) (Fin k) F) := by
  change (Matrix.of (fun i j : Fin k => hHatKernel c i (paperIndex j))).det =
    2 * (Matrix.of (fun i j : Fin k => hKernel c i (paperIndex j))).det
  rw [hHatMatrix_eq_mul, det_mul, adjacentColumnTransform_det hk]
  ring
end
end AffineDualJT
