import AffineDualJT.WeylSymmetrizer

/-! # Reindexing products over unordered pairs -/
namespace AffineDualJT
open scoped BigOperators
noncomputable section

private def permutePair {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : {p : Fin n × Fin n // p.1 < p.2}) : {p : Fin n × Fin n // p.1 < p.2} :=
  if h : σ p.val.1 < σ p.val.2 then ⟨(σ p.val.1, σ p.val.2), h⟩
  else ⟨(σ p.val.2, σ p.val.1),
    lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (σ.injective.ne p.property.ne))⟩

private theorem permutePair_inverse {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : {p : Fin n × Fin n // p.1 < p.2}) :
    permutePair σ.symm (permutePair σ p) = p := by
  rcases p with ⟨⟨a,b⟩, hab⟩
  apply Subtype.ext
  change a < b at hab
  by_cases h : σ a < σ b
  · simp [permutePair, h, hab]
  · simp [permutePair, h, not_lt.mpr hab.le]

private def pairPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    {p : Fin n × Fin n // p.1 < p.2} ≃ {p : Fin n × Fin n // p.1 < p.2} where
  toFun := permutePair σ
  invFun := permutePair σ.symm
  left_inv := permutePair_inverse σ
  right_inv := permutePair_inverse σ.symm

theorem pairProduct_permutation {F : Type*} [Field F] {n : ℕ}
    (f : Fin n → Fin n → F) (hf : ∀ a b, f a b = f b a)
    (σ : Equiv.Perm (Fin n)) :
    pairProduct (fun a b => f (σ a) (σ b)) = pairProduct f := by
  classical
  have hpair (g : Fin n → Fin n → F) : pairProduct g =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, g p.val.1 p.val.2 := by
    unfold pairProduct
    rw [← Fintype.prod_prod_type (fun p : Fin n × Fin n =>
      if p.1 < p.2 then g p.1 p.2 else 1), ← Finset.prod_filter]
    exact Finset.prod_subtype _ (by simp) _
  rw [hpair, hpair]
  have he := Equiv.prod_comp (pairPermutation σ)
    (fun p => f p.val.1 p.val.2)
  refine Eq.trans ?_ he
  apply Finset.prod_congr rfl
  intro p _
  change f (σ p.val.1) (σ p.val.2) =
    f (permutePair σ p).val.1 (permutePair σ p).val.2
  unfold permutePair
  split_ifs
  · rfl
  · exact hf _ _

end
end AffineDualJT
