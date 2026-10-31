import AffineDualJT.FiniteColumns

/-!
# The complementary finite-column blocks, Proposition 2.2

For `H={k+1,…,k+n}`, every finite column has a leading 1 and all other
folded rows lie strictly above that row. This is exactly the unit upper
triangular calculation at the end of the paper's proof. Positive width is
necessary; the zero-width blocks are handled separately in §6.1.
-/

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}

private theorem det_unit_upper (M : Matrix (Fin n) (Fin n) F)
    (hdiag : ∀ i, M i i = 1) (hupper : ∀ i j, j < i → M i j = 0) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun {i j} hij => hupper i j hij)]
  simp [hdiag]

/-- Proposition 2.2: all seven `V_H` blocks are unit upper triangular; case `C0`. -/
theorem prop_2_2_minor_VC0 (t : F) (hk : 0 < k) :
    Matrix.det (fun i j => VC0 (n:=n) (k:=k) t ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    by_cases hi : i.val = 0
    · simp only [VC0, uC, ite_eq_left hi]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VC0, uC, ite_eq_right hi]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
  · intro i j hij
    by_cases hj : j.val = 0
    · simp only [VC0, uC, ite_eq_left hj]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VC0, uC, ite_eq_right hj]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp

/-- Proposition 2.2: case `Ct`. -/
theorem prop_2_2_minor_VCt (t : F) (hk : 0 < k) :
    Matrix.det (fun i j => VCt (n:=n) (k:=k) t ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    simp only [VCt, bracketC, paperIndex, Nat.cast_add]
    split_ifs <;> first | omega | simp
  · intro i j hij
    simp only [VCt, bracketC, paperIndex, Nat.cast_add]
    split_ifs <;> first | omega | simp


/-- Proposition 2.2: case `BC`. -/
theorem prop_2_2_minor_VBC (τ : F) (hk : 0 < k) :
    Matrix.det (fun i j => VBC (n:=n) (k:=k) τ ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    by_cases hi : i.val = 0
    · simp only [VBC, uC, uCTilde, ite_eq_left hi]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBC, uC, uCTilde, ite_eq_right hi]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
  · intro i j hij
    by_cases hj : j.val = 0
    · simp only [VBC, uC, uCTilde, ite_eq_left hj]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBC, uC, uCTilde, ite_eq_right hj]
      simp only [bracketC, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp

/-- Proposition 2.2: case `B0`. -/
theorem prop_2_2_minor_VB0 (t : F) (hk : 0 < k) :
    Matrix.det (fun i j => VB0 (n:=n) (k:=k) t ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    by_cases hi : i.val = 0
    · simp only [VB0, uB, ite_eq_left hi]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VB0, uB, ite_eq_right hi]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
  · intro i j hij
    by_cases hj : j.val = 0
    · simp only [VB0, uB, ite_eq_left hj]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VB0, uB, ite_eq_right hj]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp

/-- Proposition 2.2: case `B-`. -/
theorem prop_2_2_minor_VBminus (τ : F) (hk : 0 < k) :
    Matrix.det (fun i j => VBminus (n:=n) (k:=k) τ ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    simp only [VBminus, bracketB, paperIndex, Nat.cast_add]
    split_ifs <;> first | omega | simp
  · intro i j hij
    simp only [VBminus, bracketB, paperIndex, Nat.cast_add]
    split_ifs <;> first | omega | simp


/-- Proposition 2.2: case `B+`. -/
theorem prop_2_2_minor_VBplus (t : F) (hk : 0 < k) :
    Matrix.det (fun i j => VBplus (n:=n) (k:=k) t ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    by_cases hi : i.val = 0
    · simp only [VBplus, uPlus, ite_eq_left hi]
      simp only [bracketPlus, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBplus, uPlus, ite_eq_right hi]
      simp only [bracketPlus, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
  · intro i j hij
    by_cases hj : j.val = 0
    · simp only [VBplus, uPlus, ite_eq_left hj]
      simp only [bracketPlus, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBplus, uPlus, ite_eq_right hj]
      simp only [bracketPlus, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp

/-- Proposition 2.2: case `Bt`. -/
theorem prop_2_2_minor_VBt (t : F) (hk : 0 < k) :
    Matrix.det (fun i j => VBt (n:=n) (k:=k) t ⟨k+i.1, by omega⟩ j : Matrix (Fin n) (Fin n) F) = 1 := by
  apply det_unit_upper
  · intro i
    by_cases hi : i.val = 0
    · simp only [VBt, uB, uBTilde, ite_eq_left hi]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBt, uB, uBTilde, ite_eq_right hi]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
  · intro i j hij
    by_cases hj : j.val = 0
    · simp only [VBt, uB, uBTilde, ite_eq_left hj]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp
    · simp only [VBt, uB, uBTilde, ite_eq_right hj]
      simp only [bracketB, paperIndex, Nat.cast_add]
      split_ifs <;> first | omega | simp

end
end AffineDualJT
