import AffineDualJT.Basic

/-!
# The determinant expansion used in Cauchy--Binet

This file starts the explicit Leibniz expansion of `det (A * B)` over all
intermediate-index tuples. The paper later groups this expansion by the image
of an injective tuple, producing the Cauchy--Binet sum over increasingly
ordered subsets.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix

theorem paper_det_mul_intermediate_expansion
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F) :
    (A * B).det =
      ∑ f : Fin n → Fin l, ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : F) *
          (∏ i : Fin n, A (σ i) (f i) * B (f i) i) := by
  classical
  rw [Matrix.det_apply']
  simp only [Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ]
  rw [Finset.sum_comm]

/-- Regroup the Leibniz expansion by the intermediate tuple. -/
theorem paper_det_mul_intermediate_minors
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F) :
    (A * B).det =
      ∑ f : Fin n → Fin l,
        (∏ i : Fin n, B (f i) i) * (A.submatrix id f).det := by
  rw [paper_det_mul_intermediate_expansion]
  apply Finset.sum_congr rfl
  intro f _
  calc
    (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : F) *
          (∏ i : Fin n, A (σ i) (f i) * B (f i) i))
      = ∑ σ : Equiv.Perm (Fin n),
          (∏ i : Fin n, B (f i) i) *
            (((Equiv.Perm.sign σ : ℤ) : F) *
              ∏ i : Fin n, A (σ i) (f i)) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.prod_mul_distrib]
          ring
    _ = (∏ i : Fin n, B (f i) i) *
          ∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : F) *
              ∏ i : Fin n, A (σ i) (f i) := by
          rw [Finset.mul_sum]
    _ = (∏ i : Fin n, B (f i) i) * (A.submatrix id f).det := by
          rw [Matrix.det_apply']
          congr 1

/-- Tuples with repeated intermediate indices contribute zero because the selected
columns have a repeated column. This is the alternating step in Cauchy--Binet. -/
theorem paper_det_mul_injective_intermediate
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F) :
    (A * B).det =
      ∑ f ∈ Finset.univ.filter Function.Injective,
        (∏ i : Fin n, B (f i) i) * (A.submatrix id f).det := by
  classical
  rw [paper_det_mul_intermediate_minors]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro f hf hnot
  have hninj : ¬ Function.Injective f := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    rw [Function.Injective] at hninj
    push Not at hninj
    exact hninj
  have hdet : (A.submatrix id f).det = 0 := by
    apply Matrix.det_zero_of_column_eq hne
    intro r
    simp [Matrix.submatrix_apply, hij]
  rw [hdet]
  simp

/-- For a fixed increasingly ordered subset `Q`, summing over all bijections
from `Fin n` to `Q` gives the product of the two `Q`-minors. This is the
permutation-grouping step in Cauchy--Binet. -/
theorem paper_cauchy_binet_fixed_subset
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F)
    (Q : Finset (Fin l)) (hQ : Q.card = n) :
    (∑ σ : Equiv.Perm (Fin n),
      (∏ i : Fin n, B (Q.orderEmbOfFin hQ (σ i)) i) *
        (A.submatrix id (fun i => Q.orderEmbOfFin hQ (σ i))).det) =
      (A.submatrix id (Q.orderEmbOfFin hQ)).det *
        (B.submatrix (Q.orderEmbOfFin hQ) id).det := by
  classical
  let q := Q.orderEmbOfFin hQ
  let A_Q := A.submatrix id q
  let B_Q := B.submatrix q id
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        (∏ i : Fin n, B_Q (σ i) i) *
          (A_Q.submatrix id σ).det := by
            apply Finset.sum_congr rfl
            intro σ _
            congr 2
    _ = A_Q.det * ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : F) *
          ∏ i : Fin n, B_Q (σ i) i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ _
            rw [Matrix.det_permute']
            ring
    _ = A_Q.det * B_Q.det := by
            rw [Matrix.det_apply' B_Q]

private noncomputable def paperPermOfTuple {n l : ℕ}
    (Q : Finset (Fin l)) (hQ : Q.card = n)
    (f : Fin n → Fin l) (hf : Function.Injective f)
    (himage : Finset.univ.image f = Q) : Equiv.Perm (Fin n) := by
  let φ : Fin n → Fin n := fun i =>
    (Q.orderIsoOfFin hQ).symm ⟨f i, by rw [← himage]; simp⟩
  have hφ : Function.Injective φ := by
    intro i j hij
    apply hf
    have h := congrArg (Q.orderIsoOfFin hQ) hij
    simpa [φ] using congrArg Subtype.val h
  exact Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφ)

private theorem paperPermOfTuple_spec {n l : ℕ}
    (Q : Finset (Fin l)) (hQ : Q.card = n)
    (f : Fin n → Fin l) (hf : Function.Injective f)
    (himage : Finset.univ.image f = Q) (i : Fin n) :
    Q.orderEmbOfFin hQ (paperPermOfTuple Q hQ f hf himage i) = f i := by
  simp [paperPermOfTuple, Finset.orderEmbOfFin]

/-- All injective tuples whose image is the fixed set `Q` are exactly its
increasing enumeration followed by a permutation. -/
theorem paper_det_mul_fixed_image_fiber
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F)
    (Q : Finset (Fin l)) (hQ : Q.card = n) :
    (∑ f ∈ Finset.univ.filter
      (fun f : Fin n → Fin l => Function.Injective f ∧ Finset.univ.image f = Q),
      (∏ i : Fin n, B (f i) i) * (A.submatrix id f).det) =
    ∑ σ : Equiv.Perm (Fin n),
      (∏ i : Fin n, B (Q.orderEmbOfFin hQ (σ i)) i) *
        (A.submatrix id (fun i => Q.orderEmbOfFin hQ (σ i))).det := by
  classical
  let q := Q.orderEmbOfFin hQ
  let S := Finset.univ.filter
    (fun f : Fin n → Fin l => Function.Injective f ∧ Finset.univ.image f = Q)
  let tuplePerm (f : Fin n → Fin l) (hf : f ∈ S) : Equiv.Perm (Fin n) := by
    have h : Function.Injective f ∧ Finset.univ.image f = Q := by simpa [S] using hf
    exact paperPermOfTuple Q hQ f h.1 h.2
  have tuplePerm_spec (f : Fin n → Fin l) (hf : f ∈ S) (i : Fin n) :
      q (tuplePerm f hf i) = f i := by
    dsimp [tuplePerm]
    have hdata : Function.Injective f ∧ Finset.univ.image f = Q := by
      simpa [S] using hf
    exact paperPermOfTuple_spec Q hQ f hdata.1 hdata.2 i
  refine Finset.sum_bij
    (fun f hf => tuplePerm f hf)
    (fun σ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro f hf g hg heq
    apply funext
    intro i
    calc
      f i = q (tuplePerm f hf i) := (tuplePerm_spec f hf i).symm
      _ = q (tuplePerm g hg i) := by rw [heq]
      _ = g i := tuplePerm_spec g hg i
  · intro σ _
    let f : Fin n → Fin l := fun i => q (σ i)
    have hf : Function.Injective f := q.injective.comp σ.injective
    have himage : Finset.univ.image f = Q := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Q.orderEmbOfFin_mem hQ (σ i)
      · intro hx
        have hr : x ∈ Set.range q := by
          rw [Finset.range_orderEmbOfFin]
          exact hx
        obtain ⟨j, hj⟩ := Set.mem_range.mp hr
        refine Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, ?_⟩
        simpa [f] using hj
    refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, himage⟩, ?_⟩
    apply Equiv.ext
    intro i
    apply q.injective
    rw [paperPermOfTuple_spec Q hQ f hf himage]
  · intro f hf
    have hfS : f ∈ S := by simpa [S] using hf
    have hprod : (∏ i : Fin n, B (f i) i) =
        ∏ i : Fin n, B (q (tuplePerm f hfS i)) i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [tuplePerm_spec f hfS i]
    have hmat : A.submatrix id f =
        A.submatrix id (fun i => q (tuplePerm f hfS i)) := by
      ext i j
      change A i (f j) = A i (q (tuplePerm f hfS j))
      rw [tuplePerm_spec f hfS j]
    rw [hprod, hmat]

private theorem paper_orderEmb_equiv_image {n l : ℕ}
    (Q : Finset (Fin l)) (hQ : Q.card = n) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (fun i => Q.orderEmbOfFin hQ (σ i)) = Q := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Q.orderEmbOfFin_mem hQ (σ i)
  · intro hx
    have hr : x ∈ Set.range (Q.orderEmbOfFin hQ) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨j, hj⟩ := Set.mem_range.mp hr
    refine Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, ?_⟩
    simpa using hj

private theorem paper_card_image_injective {n l : ℕ}
    (f : Fin n → Fin l) (hf : Function.Injective f) :
    (Finset.univ.image f).card = n := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

private theorem paper_orderEmb_eq_of_finset_eq {α : Type*} [LinearOrder α]
    {n : ℕ} (Q R : Finset α) (hQ : Q.card = n) (hR : R.card = n)
    (h : Q = R) : Q.orderEmbOfFin hQ = R.orderEmbOfFin hR := by
  subst R
  have hp : hQ = hR := Subsingleton.elim _ _
  subst hR
  rfl

/-- Injective intermediate tuples are in bijection with a size-`n` image subset
and a permutation of its increasing enumeration. -/
private noncomputable def paperInjectiveTupleEquiv {n l : ℕ} :
    {f : Fin n → Fin l // Function.Injective f} ≃
      ({Q : Finset (Fin l) // Q.card = n} × Equiv.Perm (Fin n)) := by
  refine
    { toFun := fun f =>
        let Q : Finset (Fin l) := Finset.univ.image f.1
        let hQ : Q.card = n := paper_card_image_injective f.1 f.2
        (⟨Q, hQ⟩, paperPermOfTuple Q hQ f.1 f.2 rfl)
      invFun := fun qσ =>
        ⟨fun i => qσ.1.1.orderEmbOfFin qσ.1.2 (qσ.2 i), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i j hij
    have hσ : qσ.2 i = qσ.2 j := (qσ.1.1.orderEmbOfFin qσ.1.2).injective hij
    exact qσ.2.injective hσ
  · intro f
    apply Subtype.ext
    funext i
    let Q : Finset (Fin l) := Finset.univ.image f.1
    let hQ : Q.card = n := paper_card_image_injective f.1 f.2
    exact paperPermOfTuple_spec Q hQ f.1 f.2 rfl i
  · rintro ⟨Q, σ⟩
    apply Prod.ext
    · apply Subtype.ext
      exact paper_orderEmb_equiv_image Q.1 Q.2 σ
    · let f : Fin n → Fin l := fun i => Q.1.orderEmbOfFin Q.2 (σ i)
      have hf : Function.Injective f := (Q.1.orderEmbOfFin Q.2).injective.comp σ.injective
      have himage : Finset.univ.image f = Q.1 := by
        simpa [f] using paper_orderEmb_equiv_image Q.1 Q.2 σ
      have hQ' := paper_card_image_injective f hf
      have hEmb := paper_orderEmb_eq_of_finset_eq
        (Finset.univ.image f) Q.1 hQ' Q.2 himage
      apply Equiv.ext
      intro i
      apply ((Finset.univ.image f).orderEmbOfFin hQ').injective
      calc
        _ = f i := paperPermOfTuple_spec (Finset.univ.image f) hQ' f hf rfl i
        _ = Q.1.orderEmbOfFin Q.2 (σ i) := rfl
        _ = (Finset.univ.image f).orderEmbOfFin hQ' (σ i) := by rw [← hEmb]

private theorem paperInjectiveTupleEquiv_spec {n l : ℕ}
    (f : {f : Fin n → Fin l // Function.Injective f}) (i : Fin n) :
    ((paperInjectiveTupleEquiv (n := n) (l := l) f).1.1.orderEmbOfFin
      (paperInjectiveTupleEquiv (n := n) (l := l) f).1.2)
      ((paperInjectiveTupleEquiv (n := n) (l := l) f).2 i) = f.1 i := by
  dsimp [paperInjectiveTupleEquiv]
  exact paperPermOfTuple_spec _ _ f.1 f.2 rfl i

/-- Full Cauchy--Binet formula, grouped by the increasingly ordered image subset. -/
theorem paper_cauchy_binet
    {F : Type*} [Field F] {n l : ℕ}
    (A : Matrix (Fin n) (Fin l) F) (B : Matrix (Fin l) (Fin n) F) :
    (A * B).det =
      ∑ Q : {Q : Finset (Fin l) // Q.card = n},
        (A.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
          (B.submatrix (Q.1.orderEmbOfFin Q.2) id).det := by
    classical
    let Inj := {f : Fin n → Fin l // Function.Injective f}
    let term (f : Fin n → Fin l) :=
      (∏ i : Fin n, B (f i) i) * (A.submatrix id f).det
    rw [paper_det_mul_injective_intermediate]
    have hsub :
        (∑ f ∈ Finset.univ.filter Function.Injective, term f) =
          ∑ f : Inj, term f.1 := by
      refine Finset.sum_bij
        (fun f hf => ⟨f, (Finset.mem_filter.mp hf).2⟩)
        (fun f _ => Finset.mem_univ _)
        ?_ ?_ ?_
      · intro f hf g hg heq
        exact congrArg Subtype.val heq
      · intro f _
        exact ⟨f.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.2⟩, rfl⟩
      · intro f hf
        rfl
    rw [hsub]
    rw [Fintype.sum_equiv (paperInjectiveTupleEquiv (n := n) (l := l))
      (fun f : Inj => (∏ i : Fin n, B (f.1 i) i) * (A.submatrix id f.1).det)
      (fun qσ => (∏ i : Fin n,
        B (qσ.1.1.orderEmbOfFin qσ.1.2 (qσ.2 i)) i) *
          (A.submatrix id (fun i => qσ.1.1.orderEmbOfFin qσ.1.2 (qσ.2 i))).det)
      (by
        intro f
        have hprod : (∏ i : Fin n, B (f.1 i) i) =
            ∏ i : Fin n, B ((paperInjectiveTupleEquiv f).1.1.orderEmbOfFin
              (paperInjectiveTupleEquiv f).1.2 ((paperInjectiveTupleEquiv f).2 i)) i := by
          apply Finset.prod_congr rfl
          intro i _
          rw [paperInjectiveTupleEquiv_spec]
        have hmat : A.submatrix id f.1 = A.submatrix id
            (fun i => (paperInjectiveTupleEquiv f).1.1.orderEmbOfFin
              (paperInjectiveTupleEquiv f).1.2 ((paperInjectiveTupleEquiv f).2 i)) := by
          ext i j
          change A i (f.1 j) = A i
            ((paperInjectiveTupleEquiv f).1.1.orderEmbOfFin
              (paperInjectiveTupleEquiv f).1.2 ((paperInjectiveTupleEquiv f).2 j))
          rw [paperInjectiveTupleEquiv_spec]
        rw [hprod, hmat])]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro Q _
    simpa only [Prod.fst, Prod.snd] using
      (paper_cauchy_binet_fixed_subset A B Q.1 Q.2)

private theorem paper_card_compl_fin {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) : Qᶜ.card = k := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]
  omega

private noncomputable def paperSubsetComplementEquiv {n k : ℕ} :
    {Q : Finset (Fin (n+k)) // Q.card = n} ≃
      {S : Finset (Fin (n+k)) // S.card = k} where
  toFun Q := ⟨Q.1ᶜ, paper_card_compl_fin Q.1 Q.2⟩
  invFun S := ⟨S.1ᶜ, by
    rw [Finset.card_compl, Fintype.card_fin, S.2]
    omega⟩
  left_inv := by intro Q; apply Subtype.ext; simp
  right_inv := by intro S; apply Subtype.ext; simp

/-- Cauchy--Binet for `Uᵀ Z`, reindexed by complementary subsets of size `n`.
This is the subset-complement reindexing used in the paper's Theorem 3.1. -/
theorem paper_cauchy_binet_complement_sum
    {F : Type*} [Field F] {n k : ℕ}
    (U Z : Matrix (Fin (n+k)) (Fin k) F) :
    (∑ Q : {Q : Finset (Fin (n+k)) // Q.card = n},
      (U.submatrix (Q.1ᶜ.orderEmbOfFin (paper_card_compl_fin Q.1 Q.2)) id).det *
        (Z.submatrix (Q.1ᶜ.orderEmbOfFin (paper_card_compl_fin Q.1 Q.2)) id).det) =
      (U.transpose * Z).det := by
  classical
  let Qs := {Q : Finset (Fin (n+k)) // Q.card = n}
  let Ss := {S : Finset (Fin (n+k)) // S.card = k}
  let f (Q : Qs) :=
    (U.submatrix (Q.1ᶜ.orderEmbOfFin (paper_card_compl_fin Q.1 Q.2)) id).det *
      (Z.submatrix (Q.1ᶜ.orderEmbOfFin (paper_card_compl_fin Q.1 Q.2)) id).det
  let g (S : Ss) :=
    (U.submatrix (S.1.orderEmbOfFin S.2) id).det *
      (Z.submatrix (S.1.orderEmbOfFin S.2) id).det
  calc
    (∑ Q : Qs, f Q) = ∑ S : Ss, g S := by
      apply Fintype.sum_equiv paperSubsetComplementEquiv f g
      intro Q
      rfl
    _ = (U.transpose * Z).det := by
      rw [paper_cauchy_binet U.transpose Z]
      apply Finset.sum_congr rfl
      intro S _
      have htranspose : U.transpose.submatrix id (S.1.orderEmbOfFin S.2) =
          (U.submatrix (S.1.orderEmbOfFin S.2) id).transpose := by
        ext i j
        rfl
      rw [htranspose, Matrix.det_transpose]

end AffineDualJT
