import AffineDualJT.AffineDetSum

/-!
# Finite row multilinearity, source.tex §3.3

Each entry has finite support. The union of the entry supports bounds each
row, and their finite Cartesian product bounds the determinant support.
Multilinearity then identifies the determinant of the entrywise sums with
the finite determinant sum (1.2), without an infinite-sum interchange.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

variable {R : Type*} [CommRing R] {k : ℕ}

private def rowSupportFinset {α : Type*} [DecidableEq α]
    (g : Fin k → Fin k → α → R)
    (hg : ∀ i j, Function.HasFiniteSupport (g i j)) (i : Fin k) : Finset α :=
  Finset.univ.biUnion fun j => (hg i j).toFinset

private theorem entry_zero_outside_rowSupport {α : Type*} [DecidableEq α]
    (g : Fin k → Fin k → α → R)
    (hg : ∀ i j, Function.HasFiniteSupport (g i j)) (i j : Fin k) (a : α)
    (ha : a ∉ rowSupportFinset g hg i) : g i j a = 0 := by
  classical
  by_contra h
  apply ha
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  exact (hg i j).mem_toFinset.mpr h

/-- The finite Cartesian product of row supports bounds the determinant support. -/
theorem det_rows_hasFiniteSupport {α : Type*}
    (g : Fin k → Fin k → α → R)
    (hg : ∀ i j, Function.HasFiniteSupport (g i j)) :
    Function.HasFiniteSupport (fun y : Fin k → α =>
      (Matrix.of fun i j => g i j (y i)).det) := by
  classical
  apply (Fintype.piFinset (rowSupportFinset g hg)).finite_toSet.subset
  intro y hy
  apply Fintype.mem_piFinset.mpr
  intro i
  by_contra hi
  exact hy (det_eq_zero_of_row_eq_zero i fun j =>
    entry_zero_outside_rowSupport g hg i j (y i) hi)

/-- Finite row multilinearity for entrywise `finsum`, as used in §3.3. -/
theorem det_finsum_rows {α : Type*}
    (g : Fin k → Fin k → α → R)
    (hg : ∀ i j, Function.HasFiniteSupport (g i j)) :
    (Matrix.of fun i j => ∑ᶠ a : α, g i j a).det =
      ∑ᶠ y : Fin k → α, (Matrix.of fun i j => g i j (y i)).det := by
  classical
  let s := rowSupportFinset g hg
  have hentry (i j : Fin k) : Function.support (g i j) ⊆ (s i : Set α) := by
    intro a ha
    by_contra hn
    exact ha (entry_zero_outside_rowSupport g hg i j a hn)
  have hdet : Function.support (fun y : Fin k → α =>
      (Matrix.of fun i j => g i j (y i)).det) ⊆
      (Fintype.piFinset s : Set (Fin k → α)) := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hy (det_eq_zero_of_row_eq_zero i fun j =>
      entry_zero_outside_rowSupport g hg i j (y i) hi)
  rw [finsum_eq_sum_of_support_subset _ hdet]
  have hrows : (Matrix.of fun i j => ∑ᶠ a : α, g i j a) =
      fun i => ∑ a ∈ s i, (fun j => g i j a) := by
    ext i j
    simpa only [Matrix.of_apply, Finset.sum_apply] using
      finsum_eq_sum_of_support_subset _ (hentry i j)
  rw [hrows]
  exact (detRowAlternating (R := R) (n := Fin k)).toMultilinearMap.map_sum_finset
    (fun i a j => g i j a) s

namespace AffineDetSum

/-- The summands of (1.2) have finite support whenever the coefficient rows do. -/
theorem jkMatrix_det_hasFiniteSupport
    (K : ℤ) (hK : K ≠ 0) (w F : Fin k → ℤ → R)
    (hF : ∀ i, Function.HasFiniteSupport (F i)) :
    Function.HasFiniteSupport (fun y : Fin k → ℤ => (jkMatrix K w F y).det) := by
  exact det_rows_hasFiniteSupport (fun i j y => w j y * F i (paperIndex j - K * y))
    (fun i j => weighted_shift_hasFiniteSupport K (paperIndex j) hK (w j) (F i) (hF i))

/-- The last step in the ordinary affine proofs: `det A = J_K`. -/
theorem det_finsum_eq_JK
    (K : ℤ) (hK : K ≠ 0) (w F : Fin k → ℤ → R)
    (hF : ∀ i, Function.HasFiniteSupport (F i)) :
    (Matrix.of fun i j => ∑ᶠ y : ℤ, w j y * F i (paperIndex j - K * y)).det =
      JK K w F := by
  exact det_finsum_rows (fun i j y => w j y * F i (paperIndex j - K * y))
    (fun i j => weighted_shift_hasFiniteSupport K (paperIndex j) hK (w j) (F i) (hF i))

end AffineDetSum
end
end AffineDualJT
