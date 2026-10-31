import AffineDualJT.MatrixBlocks
import AffineDualJT.PermutationSigns
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Tactic

/-!
# The quotient top-form steps in §3.1

This is the abstract linear-algebra step used by the paper after passing to
`F^(n+k) / col(U)`: alternating forms of top degree on an `n`-dimensional
space are determined by their value on one basis. The fixed-column form is
independent of the chosen linear section, and its evaluation on coordinate
classes agrees with the determinant formed from those coordinate vectors.
-/

namespace AffineDualJT

def paperSplitRows (n k : ℕ) : Fin k ⊕ Fin n ≃ Fin (n+k) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm k n))

private def paperQ0BlockFlip (n k : ℕ) : Equiv.Perm (Fin (n+k)) :=
  let c : Fin (k+n) ≃ Fin (n+k) := finCongr (Nat.add_comm k n)
  c.symm.trans ((paperBlockFlip k n).trans c)

private def paperQ0Split (n k : ℕ) : Fin k ⊕ Fin n ≃ Fin (n+k) :=
  (paperSplitRows n k).trans (paperQ0BlockFlip n k)

private theorem paperQ0Split_left (n k : ℕ) (i : Fin k) :
    paperQ0Split n k (Sum.inl i) = Fin.natAdd n i := by
  simp [paperQ0Split, paperQ0BlockFlip, paperSplitRows, paperBlockFlip,
    Equiv.trans_apply, finSumFinEquiv_apply_left,
    finAddFlip_apply_castAdd, finCongr_apply]

private theorem paperQ0Split_right (n k : ℕ) (i : Fin n) :
    paperQ0Split n k (Sum.inr i) = Fin.castAdd k i := by
  simp [paperQ0Split, paperQ0BlockFlip, paperSplitRows, paperBlockFlip,
    Equiv.trans_apply, finSumFinEquiv_apply_right,
    finAddFlip_apply_natAdd, finCongr_apply]

private theorem paperQ0Split_sign (n k : ℕ) :
    Equiv.Perm.sign (paperQ0Split n k |>.trans (paperSplitRows n k).symm) =
      (-1) ^ (n*k) := by
  let e := paperSplitRows n k
  let p₀ := paperQ0Split n k
  let σ := p₀.trans e.symm
  have hconj : (e.symm.trans σ).trans e = paperQ0BlockFlip n k := by
    ext i
    simp [σ, p₀, e, paperQ0Split, Equiv.trans_apply]
  have hσ : Equiv.Perm.sign σ = Equiv.Perm.sign (paperQ0BlockFlip n k) := by
    rw [← Equiv.Perm.sign_symm_trans_trans σ e, hconj]
  have hflip : Equiv.Perm.sign (paperQ0BlockFlip n k) =
      Equiv.Perm.sign (paperBlockFlip k n) := by
    unfold paperQ0BlockFlip
    rw [← Equiv.trans_assoc, Equiv.Perm.sign_symm_trans_trans]
  rw [hσ, hflip, paperBlockFlip_sign, Nat.mul_comm]

private def paperRowStack
    {F α β : Type*} [Field F]
    (A : Matrix α (α ⊕ β) F) (B : Matrix β (α ⊕ β) F) :
    Matrix (α ⊕ β) (α ⊕ β) F := fun i j =>
      match i with
      | Sum.inl a => A a j
      | Sum.inr b => B b j

private def paperCoordinateVector {F : Type*} [Zero F] [One F] {L : ℕ}
    (q : Fin L) : Fin L → F := fun j => if j = q then 1 else 0

private theorem paper_matrix_mulVec_coordinate
    {F : Type*} [Field F] {m L : ℕ}
    (X : Matrix (Fin m) (Fin L) F) (j : Fin L) :
    X.mulVecLin (paperCoordinateVector j) = X.col j := by
  rw [Matrix.mulVecLin_apply]
  have hsingle : paperCoordinateVector j = Pi.single j (1:F) := by
    ext i
    simp [paperCoordinateVector, Pi.single_apply, eq_comm]
  rw [hsingle, Matrix.mulVec_single_one]

private theorem det_fromRows_add_rowSpan
    {F α β : Type*} [Field F]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix α (α ⊕ β) F) (B : Matrix β (α ⊕ β) F) (D : Matrix β α F) :
    (paperRowStack A (D * A + B)).det =
      (paperRowStack A B).det := by
  let P : Matrix (α ⊕ β) (α ⊕ β) F := Matrix.fromBlocks 1 0 D 1
  have hmul : P * paperRowStack A B = paperRowStack A (D * A + B) := by
    ext i j
    cases i with
    | inl i => simp [P, Matrix.mul_apply, paperRowStack, Matrix.fromBlocks,
        Matrix.one_apply, Fintype.sum_sum_type]
    | inr i => simp [P, Matrix.mul_apply, paperRowStack, Matrix.fromBlocks,
        Matrix.one_apply, Fintype.sum_sum_type, add_comm]
  have hP : P.det = 1 := by
    change (Matrix.fromBlocks (1 : Matrix α α F) 0 D 1).det = 1
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one]
    simp
  calc
    _ = (P * paperRowStack A B).det := by rw [hmul]
    _ = P.det * (paperRowStack A B).det := Matrix.det_mul _ _
    _ = _ := by rw [hP]; ring

noncomputable def paperFixedColumnDetMultilinear
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : Q →ₗ[F] (Fin (n+k) → F)) : MultilinearMap F (fun _ : Fin n => Q) F := by
  let e := paperSplitRows n k
  let s' : Q →ₗ[F] (Fin k ⊕ Fin n → F) :=
    { toFun := fun q c => s q (e c)
      map_add' := by intros; ext c; simp
      map_smul' := by intros; ext c; simp }
  let d : AlternatingMap F (Fin k ⊕ Fin n → F) F (Fin k ⊕ Fin n) := Matrix.detRowAlternating
  exact ((d.toMultilinearMap.currySum
    (fun i => fun c => U (e c) i)).compLinearMap fun _ => s')

theorem paperFixedColumnDetMultilinear_apply
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : Q →ₗ[F] (Fin (n+k) → F)) (v : Fin n → Q) :
    paperFixedColumnDetMultilinear U s v =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => s (v i) (paperSplitRows n k c))).det := by
  apply congrArg Matrix.detRowAlternating
  funext r c
  cases r <;> rfl

noncomputable def paperFixedColumnDetAlternating
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : Q →ₗ[F] (Fin (n+k) → F)) : AlternatingMap F Q F (Fin n) := by
  refine ⟨paperFixedColumnDetMultilinear U s, ?_⟩
  intro v i j hij hne
  change paperFixedColumnDetMultilinear U s v = 0
  rw [paperFixedColumnDetMultilinear_apply]
  let M : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) F :=
    paperRowStack (Matrix.of fun a c => U (paperSplitRows n k c) a)
      (Matrix.of fun a c => s (v a) (paperSplitRows n k c))
  have hrne : (Sum.inr i : Fin k ⊕ Fin n) ≠ Sum.inr j := by
    intro h
    exact hne (Sum.inr.inj h)
  have hrows : M (Sum.inr i) = M (Sum.inr j) := by
    funext c
    simp [M, paperRowStack, hij]
  change M.det = 0
  exact Matrix.det_zero_of_row_eq hrne hrows

@[simp] theorem paperFixedColumnDetAlternating_apply
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : Q →ₗ[F] (Fin (n+k) → F)) (v : Fin n → Q) :
    paperFixedColumnDetAlternating U s v =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => s (v i) (paperSplitRows n k c))).det := by
  change paperFixedColumnDetMultilinear U s v = _
  exact paperFixedColumnDetMultilinear_apply U s v

theorem paperFixedColumnDetAlternating_eq_of_representatives
    {F : Type*} [Field F]
    {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) →ₗ[F]
      (Fin (n+k) → F))
    (hs : (LinearMap.range U.mulVecLin).mkQ.comp s = LinearMap.id)
    (v : Fin n → (Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin)
    (r : Fin n → (Fin (n+k) → F))
    (hr : ∀ i, (LinearMap.range U.mulVecLin).mkQ (r i) = v i) :
    paperFixedColumnDetAlternating U s v =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => r i (paperSplitRows n k c))).det := by
  classical
  let S := LinearMap.range U.mulVecLin
  have hdiff_mem (i : Fin n) : r i - s (v i) ∈ S := by
    have hs_i : S.mkQ (s (v i)) = v i := by
      change (S.mkQ.comp s) (v i) = v i
      rw [hs]
      simp
    have hr_i : S.mkQ (r i) = v i := hr i
    have hz : S.mkQ (r i - s (v i)) = 0 := by
      rw [map_sub, hr_i, hs_i]
      simp
    have hk : r i - s (v i) ∈ S.mkQ.ker := LinearMap.mem_ker.mpr hz
    simpa [S, Submodule.ker_mkQ] using hk
  have hcoeff_exists (i : Fin n) :
      ∃ c : Fin k → F, U.mulVecLin c = r i - s (v i) := by
    exact LinearMap.mem_range.mp (hdiff_mem i)
  let coeff (i : Fin n) : Fin k → F := Classical.choose (hcoeff_exists i)
  have hcoeff (i : Fin n) : U.mulVecLin (coeff i) = r i - s (v i) :=
    Classical.choose_spec (hcoeff_exists i)
  let e := paperSplitRows n k
  let A : Matrix (Fin k) (Fin k ⊕ Fin n) F := fun a c => U (e c) a
  let Bs : Matrix (Fin n) (Fin k ⊕ Fin n) F := fun i c => s (v i) (e c)
  let Br : Matrix (Fin n) (Fin k ⊕ Fin n) F := fun i c => r i (e c)
  let D : Matrix (Fin n) (Fin k) F := fun i a => coeff i a
  have hrows : Br = D * A + Bs := by
    ext i c
    have hc := congrFun (hcoeff i) (e c)
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at hc
    change r i (e c) =
      (∑ a : Fin k, coeff i a * U (e c) a) + s (v i) (e c)
    have hsum : (∑ a : Fin k, coeff i a * U (e c) a) =
        ∑ a : Fin k, U (e c) a * coeff i a := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    calc
      r i (e c) = (r i - s (v i)) (e c) + s (v i) (e c) := by
        simpa only [Pi.sub_apply] using sub_add_cancel (r i (e c)) (s (v i) (e c)) |>.symm
      _ = (∑ a : Fin k, U (e c) a * coeff i a) + s (v i) (e c) := by rw [← hc]
      _ = (∑ a : Fin k, coeff i a * U (e c) a) + s (v i) (e c) := by rw [← hsum]
  rw [paperFixedColumnDetAlternating_apply]
  change (paperRowStack A Bs).det = (paperRowStack A Br).det
  rw [hrows]
  exact (det_fromRows_add_rowSpan A Bs D).symm

theorem paperFixedColumnDetAlternating_section_eq
    {F : Type*} [Field F] {n k : ℕ}
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (s t : ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) →ₗ[F]
      (Fin (n+k) → F))
    (hs : (LinearMap.range U.mulVecLin).mkQ.comp s = LinearMap.id)
    (ht : (LinearMap.range U.mulVecLin).mkQ.comp t = LinearMap.id)
    (v : Fin n → (Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) :
    paperFixedColumnDetAlternating U s v = paperFixedColumnDetAlternating U t v := by
  rw [paperFixedColumnDetAlternating_eq_of_representatives U s hs v (fun i => t (v i))]
  · symm
    rw [paperFixedColumnDetAlternating_eq_of_representatives U t ht v (fun i => t (v i))]
    intro i
    change ((LinearMap.range U.mulVecLin).mkQ.comp t) (v i) = v i
    rw [ht]
    simp
  · intro i
    change ((LinearMap.range U.mulVecLin).mkQ.comp t) (v i) = v i
    rw [ht]
    simp

theorem paperFixedColumnDetAlternating_coordinate
    {F : Type*} [Field F] {n k : ℕ}
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) →ₗ[F]
      (Fin (n+k) → F))
    (hs : (LinearMap.range U.mulVecLin).mkQ.comp s = LinearMap.id)
    (q : Fin n → Fin (n+k)) :
    paperFixedColumnDetAlternating U s
        (fun i => (LinearMap.range U.mulVecLin).mkQ (paperCoordinateVector (q i))) =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => paperCoordinateVector (q i) (paperSplitRows n k c))).det := by
  apply paperFixedColumnDetAlternating_eq_of_representatives U s hs
  intro i
  rfl

theorem paper_coordinate_augmented_det
    {F : Type*} [Field F] {n k : ℕ}
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
      (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
        (paperSplitRows n k c))).det =
      ((Equiv.Perm.sign (p.trans (paperSplitRows n k).symm) : ℤ) : F) *
        (U.submatrix (fun j : Fin k => p (Sum.inl j)) id).det := by
  classical
  let e := paperSplitRows n k
  let σ : Equiv.Perm (Fin k ⊕ Fin n) := p.trans e.symm
  let A₁ : Matrix (Fin k) (Fin k) F := fun i j => U (p (Sum.inl j)) i
  let A₂ : Matrix (Fin k) (Fin n) F := fun i j => U (p (Sum.inr j)) i
  let M : Matrix (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) F :=
    paperRowStack (Matrix.of fun i c => U (e c) i)
      (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i)) (e c))
  have hblock : M.submatrix id σ = Matrix.fromBlocks A₁ A₂ 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [M, paperRowStack, σ, e, A₁,
          Matrix.fromBlocks, Matrix.of_apply]
      | inr j => simp [M, paperRowStack, σ, e, A₂,
          Matrix.fromBlocks, Matrix.of_apply]
    | inr i =>
      cases j with
      | inl j =>
        have hne : p (Sum.inl j) ≠ p (Sum.inr i) := by
          intro h
          have h' := p.injective h
          exact Sum.inl_ne_inr h'
        simp [M, paperRowStack, σ, e, paperCoordinateVector,
          Matrix.fromBlocks, Matrix.of_apply, hne]
      | inr j =>
        simp [M, paperRowStack, σ, e, paperCoordinateVector,
          Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply, eq_comm]
  have hdet_reindex : M.det =
      ((Equiv.Perm.sign σ : ℤ) : F) * (M.submatrix id σ).det := by
    have hd := Matrix.det_permute' σ.symm (M.submatrix id σ)
    have hmat : (M.submatrix id σ).submatrix id σ.symm = M := by
      ext i j
      simp [Matrix.submatrix]
    rw [hmat, ← Equiv.Perm.inv_def, Equiv.Perm.sign_inv] at hd
    exact hd
  change M.det = _
  rw [hdet_reindex, hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  have hA₁ : A₁ = (U.submatrix (fun j : Fin k => p (Sum.inl j)) id).transpose := by
    ext i j
    rfl
  rw [hA₁, Matrix.det_transpose]

noncomputable def paperImageTopForm
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n : ℕ} (e : Q ≃ₗ[F] (Fin n → F)) : AlternatingMap F Q F (Fin n) :=
  Matrix.detRowAlternating.compLinearMap e.toLinearMap

theorem paper_quotient_induced_map_injective
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (S : Submodule F V) (f : V →ₗ[F] W) (hS : S = LinearMap.ker f) :
    Function.Injective (S.liftQ f hS.le) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_liftQ_eq_bot' S f hS]

theorem paper_quotient_has_linear_section
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (S : Submodule F V) :
    ∃ s : (V ⧸ S) →ₗ[F] V, S.mkQ.comp s = LinearMap.id := by
  obtain ⟨s, hs⟩ := S.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr S.mkQ_surjective)
  exact ⟨s, hs⟩

theorem paper_matrix_image_in_kernel
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F) (hXU : X * U = 0) :
    LinearMap.range U.mulVecLin ≤ LinearMap.ker X.mulVecLin := by
  rw [LinearMap.range_le_ker_iff]
  rw [← Matrix.mulVecLin_mul, hXU, Matrix.mulVecLin_zero]

theorem paper_matrix_range_eq_kernel
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0) :
    LinearMap.range U.mulVecLin = LinearMap.ker X.mulVecLin := by
  have hXminor : (firstCols X).rank ≤ X.rank := by
    change (X.submatrix id (Fin.castAdd k)).rank ≤ X.rank
    exact Matrix.rank_submatrix_le X id (Fin.castAdd k)
  have hXrank : X.rank = n := by
    apply Nat.le_antisymm
    · simpa using X.rank_le_card_height
    · have hdet := Matrix.rank_of_det_ne_zero hXQ0
      simpa using hdet.symm.trans_le hXminor
  have hUminor : (tailRowsAfterN U).rank ≤ U.rank := by
    change (U.submatrix (Fin.natAdd n) id).rank ≤ U.rank
    exact Matrix.rank_submatrix_le U (Fin.natAdd n) id
  have hUrank : U.rank = k := by
    apply Nat.le_antisymm
    · simpa using U.rank_le_width
    · have hdet := Matrix.rank_of_det_ne_zero hUJ
      simpa using hdet.symm.trans_le hUminor
  have hXker : Module.finrank F (LinearMap.ker X.mulVecLin) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [← Matrix.rank, hXrank] at h
    simpa [Module.finrank_pi] using h
  have hUrng : Module.finrank F (LinearMap.range U.mulVecLin) = k := by
    simpa [Matrix.rank] using hUrank
  apply Submodule.eq_of_le_of_finrank_eq (paper_matrix_image_in_kernel X U hXU)
  rw [hUrng, hXker]

noncomputable def paper_matrix_quotient_equiv
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0) :
    ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) ≃ₗ[F] (Fin n → F) := by
  let S := LinearMap.range U.mulVecLin
  have hS : S = LinearMap.ker X.mulVecLin :=
    paper_matrix_range_eq_kernel X U hXU hXQ0 hUJ
  let xbar : (Fin (n+k) → F) ⧸ S →ₗ[F] (Fin n → F) :=
    S.liftQ X.mulVecLin (paper_matrix_image_in_kernel X U hXU)
  have hinj : Function.Injective xbar := by
    apply paper_quotient_induced_map_injective S X.mulVecLin hS
  have hdim : Module.finrank F ((Fin (n+k) → F) ⧸ S) =
      Module.finrank F (Fin n → F) := by
    have hq := S.finrank_quotient_add_finrank
    have hu : Module.finrank F S = k := by
      simpa [S, Matrix.rank] using (show U.rank = k from by
        apply Nat.le_antisymm
        · simpa using U.rank_le_width
        · have hm : (tailRowsAfterN U).rank ≤ U.rank := by
            change (U.submatrix (Fin.natAdd n) id).rank ≤ U.rank
            exact Matrix.rank_submatrix_le U (Fin.natAdd n) id
          have hdet := (Matrix.rank_of_det_ne_zero hUJ).symm.trans_le hm
          simpa using hdet)
    rw [hu] at hq
    have hq' : Module.finrank F ((Fin (n+k) → F) ⧸ S) + k = n+k := by
      simpa [Module.finrank_pi] using hq
    have hdim' : Module.finrank F ((Fin (n+k) → F) ⧸ S) = n := by omega
    simpa [Module.finrank_pi] using hdim'
  exact LinearMap.linearEquivOfInjective xbar hinj hdim

theorem paper_matrix_quotient_equiv_mkQ_apply
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (v : Fin (n+k) → F) :
    paper_matrix_quotient_equiv X U hXU hXQ0 hUJ
      ((LinearMap.range U.mulVecLin).mkQ v) = X.mulVecLin v := by
  unfold paper_matrix_quotient_equiv
  rw [LinearMap.linearEquivOfInjective_apply]
  change ((LinearMap.range U.mulVecLin).liftQ X.mulVecLin
    (paper_matrix_image_in_kernel X U hXU))
      ((LinearMap.range U.mulVecLin).mkQ v) = X.mulVecLin v
  rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]

theorem paper_matrix_quotient_equiv_coordinate_apply
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (j : Fin (n+k)) :
    paper_matrix_quotient_equiv X U hXU hXQ0 hUJ
      ((LinearMap.range U.mulVecLin).mkQ (paperCoordinateVector j)) = X.col j := by
  rw [paper_matrix_quotient_equiv_mkQ_apply, paper_matrix_mulVec_coordinate]

theorem paper_transpose_range_eq_kernel
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0) :
    LinearMap.range Z.mulVecLin = LinearMap.ker Y.transpose.mulVecLin := by
  have hYminor : (lastRowsY Y).rank ≤ Y.transpose.rank := by
    have hm : (lastRowsY Y).rank ≤ Y.rank := by
      have he : lastRowsY Y = Y.submatrix (fun i : Fin n => ⟨k + i.1, by omega⟩) id := by
        ext i j
        rfl
      rw [he]
      exact Matrix.rank_submatrix_le Y (fun i : Fin n => ⟨k + i.1, by omega⟩) id
    rw [Matrix.rank_transpose]
    exact hm
  have hYrank : Y.transpose.rank = n := by
    apply Nat.le_antisymm
    · simpa using Y.transpose.rank_le_card_height
    · have hdet := (Matrix.rank_of_det_ne_zero hYH).symm.trans_le hYminor
      simpa using hdet
  have hZminor : (firstRowsZ Z).rank ≤ Z.rank := by
    have he : firstRowsZ Z = Z.submatrix (fun i : Fin k => ⟨i.1, by omega⟩) id := by
      ext i j
      rfl
    rw [he]
    exact Matrix.rank_submatrix_le Z (fun i : Fin k => ⟨i.1, by omega⟩) id
  have hZrank : Z.rank = k := by
    apply Nat.le_antisymm
    · simpa using Z.rank_le_width
    · have hdet := (Matrix.rank_of_det_ne_zero hZI).symm.trans_le hZminor
      simpa using hdet
  have hYker : Module.finrank F (LinearMap.ker Y.transpose.mulVecLin) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker Y.transpose.mulVecLin
    rw [← Matrix.rank, hYrank] at h
    simpa [Module.finrank_pi] using h
  have hZrng : Module.finrank F (LinearMap.range Z.mulVecLin) = k := by
    simpa [Matrix.rank] using hZrank
  have hYZmap : Y.transpose.mulVecLin.comp Z.mulVecLin = 0 := by
    rw [← Matrix.mulVecLin_mul, hYTZ, Matrix.mulVecLin_zero]
  apply Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.mpr hYZmap)
  rw [hZrng, hYker]

noncomputable def paper_transpose_quotient_equiv
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0) :
    ((Fin (n+k) → F) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[F] (Fin n → F) := by
  let S := LinearMap.range Z.mulVecLin
  have hS : S = LinearMap.ker Y.transpose.mulVecLin :=
    paper_transpose_range_eq_kernel Y Z hYTZ hYH hZI
  let ybar : (Fin (n+k) → F) ⧸ S →ₗ[F] (Fin n → F) :=
    S.liftQ Y.transpose.mulVecLin (paper_matrix_image_in_kernel Y.transpose Z hYTZ)
  have hinj : Function.Injective ybar := by
    apply paper_quotient_induced_map_injective S Y.transpose.mulVecLin hS
  have hdim : Module.finrank F ((Fin (n+k) → F) ⧸ S) =
      Module.finrank F (Fin n → F) := by
    have hq := S.finrank_quotient_add_finrank
    have hu : Module.finrank F S = k := by
      have hm : (firstRowsZ Z).rank ≤ Z.rank := by
        have he : firstRowsZ Z = Z.submatrix
            (fun i : Fin k => ⟨i.1, by omega⟩) id := by
          ext i j
          rfl
        rw [he]
        exact Matrix.rank_submatrix_le Z (fun i : Fin k => ⟨i.1, by omega⟩) id
      have hzr : Z.rank = k := by
        apply Nat.le_antisymm
        · simpa using Z.rank_le_width
        · have hd := (Matrix.rank_of_det_ne_zero hZI).symm.trans_le hm
          simpa using hd
      simpa [S, Matrix.rank] using hzr
    rw [hu] at hq
    have hq' : Module.finrank F ((Fin (n+k) → F) ⧸ S) + k = n+k := by
      simpa [Module.finrank_pi] using hq
    have hdim' : Module.finrank F ((Fin (n+k) → F) ⧸ S) = n := by omega
    simpa [Module.finrank_pi] using hdim'
  exact LinearMap.linearEquivOfInjective ybar hinj hdim

theorem paper_transpose_quotient_equiv_coordinate_apply
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0)
    (j : Fin (n+k)) :
    paper_transpose_quotient_equiv Y Z hYTZ hYH hZI
      ((LinearMap.range Z.mulVecLin).mkQ (paperCoordinateVector j)) =
        Y.transpose.col j := by
  unfold paper_transpose_quotient_equiv
  rw [LinearMap.linearEquivOfInjective_apply]
  change ((LinearMap.range Z.mulVecLin).liftQ Y.transpose.mulVecLin
    (paper_matrix_image_in_kernel Y.transpose Z hYTZ))
      ((LinearMap.range Z.mulVecLin).mkQ (paperCoordinateVector j)) = _
  rw [← LinearMap.comp_apply, Submodule.liftQ_mkQ]
  exact paper_matrix_mulVec_coordinate Y.transpose j

theorem topAlternatingForms_proportional
    {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F M)
    (f g : M [⋀^ι]→ₗ[F] F)
    (hg : g (fun i => b i) ≠ 0) :
    f = ((f (fun i => b i) / g (fun i => b i)) • g) := by
  classical
  apply Module.Basis.ext_alternating b
  intro v hv
  let e : Equiv.Perm ι := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  have hf := f.map_perm (fun i => b i) e
  have hg' := g.map_perm (fun i => b i) e
  change f (fun i => b (v i)) = Equiv.Perm.sign e • f (fun i => b i) at hf
  change g (fun i => b (v i)) = Equiv.Perm.sign e • g (fun i => b i) at hg'
  change f (fun i => b (v i)) =
    (f (fun i => b i) / g (fun i => b i)) • g (fun i => b (v i))
  rw [hf, hg']
  simp only [Units.smul_def, smul_eq_mul]
  field_simp [hg]
  ring

theorem paper_quotient_top_forms_proportional
    {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q]
    {n k : ℕ} (e : Q ≃ₗ[F] (Fin n → F))
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (s : Q →ₗ[F] (Fin (n+k) → F)) :
    paperFixedColumnDetAlternating U s =
      (paperFixedColumnDetAlternating U s
        (fun i => (Module.Basis.map (Pi.basisFun F (Fin n)) e.symm) i) /
          paperImageTopForm e
            (fun i => (Module.Basis.map (Pi.basisFun F (Fin n)) e.symm) i)) •
        paperImageTopForm e := by
  let b : Module.Basis (Fin n) F Q :=
    (Pi.basisFun F (Fin n)).map e.symm
  have hb : paperImageTopForm e (fun i => b i) = 1 := by
    change Matrix.det (Matrix.of fun i j => e (b i) j) = 1
    have hmat : Matrix.of (fun i j => e (b i) j : Matrix (Fin n) (Fin n) F) = 1 := by
      ext i j
      simp [b, Module.Basis.map_apply, Pi.basisFun_apply, Pi.single_apply,
        Matrix.one_apply, eq_comm]
    rw [hmat, Matrix.det_one]
  have hne : paperImageTopForm e (fun i => b i) ≠ 0 := by
    rw [hb]
    exact one_ne_zero
  simpa [b] using
    (topAlternatingForms_proportional b (paperFixedColumnDetAlternating U s)
      (paperImageTopForm e) hne)

theorem paper_XU_quotient_forms_proportional
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0) :
    ∃ s : ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) →ₗ[F]
        (Fin (n+k) → F),
      (LinearMap.range U.mulVecLin).mkQ.comp s = LinearMap.id ∧
      paperFixedColumnDetAlternating U s =
        (paperFixedColumnDetAlternating U s
          (fun i => (Module.Basis.map (Pi.basisFun F (Fin n))
            (paper_matrix_quotient_equiv X U hXU hXQ0 hUJ).symm) i) /
          paperImageTopForm (paper_matrix_quotient_equiv X U hXU hXQ0 hUJ)
            (fun i => (Module.Basis.map (Pi.basisFun F (Fin n))
              (paper_matrix_quotient_equiv X U hXU hXQ0 hUJ).symm) i)) •
          paperImageTopForm (paper_matrix_quotient_equiv X U hXU hXQ0 hUJ) := by
  let S := LinearMap.range U.mulVecLin
  let e := paper_matrix_quotient_equiv X U hXU hXQ0 hUJ
  obtain ⟨s, hs⟩ := paper_quotient_has_linear_section S
  exact ⟨s, hs, paper_quotient_top_forms_proportional e U s⟩

theorem paper_YZ_quotient_forms_proportional
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0) :
    ∃ s : ((Fin (n+k) → F) ⧸ LinearMap.range Z.mulVecLin) →ₗ[F]
        (Fin (n+k) → F),
      (LinearMap.range Z.mulVecLin).mkQ.comp s = LinearMap.id ∧
      paperFixedColumnDetAlternating Z s =
        (paperFixedColumnDetAlternating Z s
          (fun i => (Module.Basis.map (Pi.basisFun F (Fin n))
            (paper_transpose_quotient_equiv Y Z hYTZ hYH hZI).symm) i) /
          paperImageTopForm (paper_transpose_quotient_equiv Y Z hYTZ hYH hZI)
            (fun i => (Module.Basis.map (Pi.basisFun F (Fin n))
              (paper_transpose_quotient_equiv Y Z hYTZ hYH hZI).symm) i)) •
          paperImageTopForm (paper_transpose_quotient_equiv Y Z hYTZ hYH hZI) := by
  let S := LinearMap.range Z.mulVecLin
  let e := paper_transpose_quotient_equiv Y Z hYTZ hYH hZI
  obtain ⟨s, hs⟩ := paper_quotient_has_linear_section S
  exact ⟨s, hs, paper_quotient_top_forms_proportional e Z s⟩

theorem paper_quotient_coordinate_minor_relation
    {F : Type*} [Field F] {n k : ℕ}
    (M : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (E : ((Fin (n+k) → F) ⧸ LinearMap.range U.mulVecLin) ≃ₗ[F]
      (Fin n → F))
    (hcoord : ∀ j, E ((LinearMap.range U.mulVecLin).mkQ
      (paperCoordinateVector j)) = M.col j)
    (p₀ p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => M i (p (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p₀ (Sum.inr i))
            (paperSplitRows n k c))).det =
      (Matrix.of fun i j => M i (p₀ (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
            (paperSplitRows n k c))).det := by
  classical
  let S := LinearMap.range U.mulVecLin
  let e := E
  obtain ⟨s, hs⟩ := paper_quotient_has_linear_section S
  let G : AlternatingMap F ((Fin (n+k) → F) ⧸ S) F (Fin n) :=
    paperFixedColumnDetAlternating U s
  let H : AlternatingMap F ((Fin (n+k) → F) ⧸ S) F (Fin n) := paperImageTopForm e
  let c := G (fun i => (Module.Basis.map (Pi.basisFun F (Fin n)) e.symm) i) /
      H (fun i => (Module.Basis.map (Pi.basisFun F (Fin n)) e.symm) i)
  have hprop : G = c • H := by
    simpa [G, H, c] using paper_quotient_top_forms_proportional e U s
  let v (p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
      Fin n → ((Fin (n+k) → F) ⧸ S) := fun i =>
        S.mkQ (paperCoordinateVector (p (Sum.inr i)))
  have hG₀ : G (v p₀) =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => paperCoordinateVector (p₀ (Sum.inr i))
          (paperSplitRows n k c))).det := by
    simpa [G, v, S] using
      paperFixedColumnDetAlternating_coordinate U s hs (fun i => p₀ (Sum.inr i))
  have hG : G (v p) =
      (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
        (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
          (paperSplitRows n k c))).det := by
    simpa [G, v, S] using
      paperFixedColumnDetAlternating_coordinate U s hs (fun i => p (Sum.inr i))
  have hH₀ : H (v p₀) = (Matrix.of fun i j => M i (p₀ (Sum.inr j))).det := by
    change Matrix.det (Matrix.of fun i j => e (v p₀ i) j) = _
    have hmat : Matrix.of (fun i j => e (v p₀ i) j : Matrix (Fin n) (Fin n) F) =
        (Matrix.of fun i j => M i (p₀ (Sum.inr j))).transpose := by
      ext i j
      change e ((LinearMap.range U.mulVecLin).mkQ
        (paperCoordinateVector (p₀ (Sum.inr i)))) j = _
      have hc := congrFun (hcoord (p₀ (Sum.inr i))) j
      simpa [e] using hc
    rw [hmat, Matrix.det_transpose]
  have hH : H (v p) = (Matrix.of fun i j => M i (p (Sum.inr j))).det := by
    change Matrix.det (Matrix.of fun i j => e (v p i) j) = _
    have hmat : Matrix.of (fun i j => e (v p i) j : Matrix (Fin n) (Fin n) F) =
        (Matrix.of fun i j => M i (p (Sum.inr j))).transpose := by
      ext i j
      change e ((LinearMap.range U.mulVecLin).mkQ
        (paperCoordinateVector (p (Sum.inr i)))) j = _
      have hc := congrFun (hcoord (p (Sum.inr i))) j
      simpa [e] using hc
    rw [hmat, Matrix.det_transpose]
  have hprop₀ : G (v p₀) = c * H (v p₀) := by
    have h := congrArg (fun f : AlternatingMap F ((Fin (n+k) → F) ⧸ S) F (Fin n) => f (v p₀)) hprop
    simpa [smul_eq_mul] using h
  have hprop' : G (v p) = c * H (v p) := by
    have h := congrArg (fun f : AlternatingMap F ((Fin (n+k) → F) ⧸ S) F (Fin n) => f (v p)) hprop
    simpa [smul_eq_mul] using h
  have hcross : G (v p) * H (v p₀) = G (v p₀) * H (v p) := by
    rw [hprop', hprop₀]
    ring
  calc
    (Matrix.of fun i j => M i (p (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p₀ (Sum.inr i))
            (paperSplitRows n k c))).det =
      G (v p₀) * H (v p) := by rw [hG₀, hH]; ring
    _ = G (v p) * H (v p₀) := hcross.symm
    _ = (Matrix.of fun i j => M i (p₀ (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
            (paperSplitRows n k c))).det := by rw [hG, hH₀]; ring

theorem paper_XU_coordinate_minor_relation
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (p₀ p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => X i (p (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p₀ (Sum.inr i))
            (paperSplitRows n k c))).det =
      (Matrix.of fun i j => X i (p₀ (Sum.inr j))).det *
        (paperRowStack (Matrix.of fun i c => U (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
            (paperSplitRows n k c))).det := by
  exact paper_quotient_coordinate_minor_relation X U
    (paper_matrix_quotient_equiv X U hXU hXQ0 hUJ)
    (fun j => paper_matrix_quotient_equiv_coordinate_apply X U hXU hXQ0 hUJ j)
    p₀ p

theorem paper_YZ_coordinate_minor_relation
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0)
    (p₀ p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => Y (p (Sum.inr i)) j).det *
        (paperRowStack (Matrix.of fun i c => Z (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p₀ (Sum.inr i))
            (paperSplitRows n k c))).det =
      (Matrix.of fun i j => Y (p₀ (Sum.inr i)) j).det *
        (paperRowStack (Matrix.of fun i c => Z (paperSplitRows n k c) i)
          (Matrix.of fun i c => paperCoordinateVector (p (Sum.inr i))
            (paperSplitRows n k c))).det := by
  have h := paper_quotient_coordinate_minor_relation Y.transpose Z
    (paper_transpose_quotient_equiv Y Z hYTZ hYH hZI)
    (fun j => paper_transpose_quotient_equiv_coordinate_apply Y Z hYTZ hYH hZI j)
    p₀ p
  have hminor (p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
      (Matrix.of fun i j => Y.transpose i (p (Sum.inr j))).det =
        (Matrix.of fun i j => Y (p (Sum.inr i)) j).det := by
    have he : Matrix.of (fun i j => Y.transpose i (p (Sum.inr j)) :
        Matrix (Fin n) (Fin n) F) =
        (Matrix.of fun i j => Y (p (Sum.inr i)) j).transpose := by
      ext i j
      rfl
    rw [he, Matrix.det_transpose]
  simpa only [hminor p, hminor p₀] using h

theorem paper_XU_complementary_minor_relation
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (p₀ p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => X i (p (Sum.inr j))).det *
        (((Equiv.Perm.sign (p₀.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (U.submatrix (fun i : Fin k => p₀ (Sum.inl i)) id).det) =
      (Matrix.of fun i j => X i (p₀ (Sum.inr j))).det *
        (((Equiv.Perm.sign (p.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (U.submatrix (fun i : Fin k => p (Sum.inl i)) id).det) := by
  have h := paper_XU_coordinate_minor_relation X U hXU hXQ0 hUJ p₀ p
  rw [paper_coordinate_augmented_det U p₀,
    paper_coordinate_augmented_det U p] at h
  exact h

theorem paper_YZ_complementary_minor_relation
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0)
    (p₀ p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => Y (p (Sum.inr i)) j).det *
        (((Equiv.Perm.sign (p₀.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (Z.submatrix (fun i : Fin k => p₀ (Sum.inl i)) id).det) =
      (Matrix.of fun i j => Y (p₀ (Sum.inr i)) j).det *
        (((Equiv.Perm.sign (p.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (Z.submatrix (fun i : Fin k => p (Sum.inl i)) id).det) := by
  have h := paper_YZ_coordinate_minor_relation Y Z hYTZ hYH hZI p₀ p
  rw [paper_coordinate_augmented_det Z p₀,
    paper_coordinate_augmented_det Z p] at h
  exact h

theorem paper_XU_standard_complement_relation
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => X i (p (Sum.inr j))).det *
        ((-1:F)^(n*k) * (tailRowsAfterN U).det) =
      (firstCols X).det *
        (((Equiv.Perm.sign (p.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (U.submatrix (fun i : Fin k => p (Sum.inl i)) id).det) := by
  have h := paper_XU_complementary_minor_relation X U hXU hXQ0 hUJ
    (paperQ0Split n k) p
  have hX0 : (Matrix.of fun i j => X i ((paperQ0Split n k) (Sum.inr j))).det =
      (firstCols X).det := by
    apply congrArg Matrix.det
    ext i j
    have hj : paperQ0Split n k (Sum.inr j) = (⟨j.1, by omega⟩ : Fin (n+k)) := by
      apply Fin.ext
      simp [paperQ0Split_right]
    change X i ((paperQ0Split n k) (Sum.inr j)) = X i ⟨j.1, by omega⟩
    exact congrArg (X i) hj
  have hU0 : U.submatrix (fun i : Fin k => (paperQ0Split n k) (Sum.inl i)) id =
      tailRowsAfterN U := by
    ext i j
    have hi : paperQ0Split n k (Sum.inl i) = (⟨n + i.1, by omega⟩ : Fin (n+k)) := by
      apply Fin.ext
      simp [paperQ0Split_left]
    change U ((paperQ0Split n k) (Sum.inl i)) j = U ⟨n + i.1, by omega⟩ j
    exact congrArg (fun r : Fin (n+k) => U r j) hi
  have hsign :
      ((Equiv.Perm.sign ((paperQ0Split n k).trans (paperSplitRows n k).symm) : ℤ) : F) =
        (-1:F)^(n*k) := by
    have hs := congrArg (fun z : ℤˣ => ((z : ℤ) : F)) (paperQ0Split_sign n k)
    simpa using hs
  rw [hX0, hU0, hsign] at h
  exact h

theorem paper_YZ_standard_complement_relation
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0)
    (p : (Fin k ⊕ Fin n) ≃ Fin (n+k)) :
    (Matrix.of fun i j => Y (p (Sum.inr i)) j).det * (firstRowsZ Z).det =
      (lastRowsY Y).det *
        (((Equiv.Perm.sign (p.trans (paperSplitRows n k).symm) : ℤ) : F) *
          (Z.submatrix (fun i : Fin k => p (Sum.inl i)) id).det) := by
  have h := paper_YZ_complementary_minor_relation Y Z hYTZ hYH hZI
    (paperSplitRows n k) p
  have hY0 : (Matrix.of fun i j => Y ((paperSplitRows n k) (Sum.inr i)) j).det =
      (lastRowsY Y).det := by
    apply congrArg Matrix.det
    ext i j
    change Y ((paperSplitRows n k) (Sum.inr i)) j =
      Y (⟨k + i.1, by omega⟩ : Fin (n+k)) j
    apply congrArg (fun r : Fin (n+k) => Y r j)
    apply Fin.ext
    simp [paperSplitRows, finSumFinEquiv_apply_right, Fin.natAdd]
  have hZ0 : Z.submatrix
      (fun i : Fin k => (paperSplitRows n k) (Sum.inl i)) id = firstRowsZ Z := by
    ext i j
    change Z ((paperSplitRows n k) (Sum.inl i)) j =
      Z (⟨i.1, by omega⟩ : Fin (n+k)) j
    apply congrArg (fun r : Fin (n+k) => Z r j)
    apply Fin.ext
    simp [paperSplitRows, finSumFinEquiv_apply_left, Fin.castAdd]
  rw [hY0, hZ0] at h
  simpa using h

/-- The X/U complementary-minor relation for an arbitrary ordered subset Q.
The indexing equivalence is the paper's increasing order on Q and Qᶜ. -/
private theorem paper_complement_card
    {n k : ℕ} (Q : Finset (Fin (n+k))) (hQ : Q.card = n) : Qᶜ.card = k := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]
  omega

def paperFinsetSplit {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) : Fin k ⊕ Fin n ≃ Fin (n+k) :=
  finSumEquivOfFinset (paper_complement_card Q hQ) (by simpa using hQ)

/-- The subset sign `ε(Q)` from the proof of Theorem 3.1.  The paper numbers
the elements of `Q` and their positions starting at 1; subtracting those
indices gives the same exponent as this zero-based `Fin` expression. -/
def paperEpsilon {n k : ℕ} (Q : Finset (Fin (n+k))) (hQ : Q.card = n) : ℤˣ :=
  (-1 : ℤˣ) ^ (∑ r : Fin n, ((Q.orderEmbOfFin hQ r).val - r.val))

/-- Among the elements of an increasingly ordered `Q`, exactly the first `r`
lie strictly before its `r`th element. -/
private theorem paper_card_Q_before {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) (r : Fin n) :
    (Q.filter (fun x => x < Q.orderEmbOfFin hQ r)).card = r.val := by
  classical
  let e := Q.orderEmbOfFin hQ
  have hset : Q = (Finset.univ : Finset (Fin n)).map e.toEmbedding := by
    symm
    exact Finset.map_orderEmbOfFin_univ Q hQ
  have hf : Q.filter (fun x => x < e r) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => e i < e r)).map e.toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxQ, hxlt⟩
      have hxmap : x ∈ (Finset.univ : Finset (Fin n)).map e.toEmbedding := by
        rw [← hset]
        exact hxQ
      rcases Finset.mem_map.mp hxmap with ⟨i, _, hix⟩
      subst x
      exact ⟨i, hxlt, rfl⟩
    · rintro ⟨i, hil, rfl⟩
      have hmem : e i ∈ Q := by
        rw [hset]
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact ⟨hmem, hil⟩
  rw [hf, Finset.card_map]
  have hfilter : (Finset.univ : Finset (Fin n)).filter (fun i => e i < e r) =
      Finset.Iio r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact e.lt_iff_lt
  rw [hfilter]
  simp

/-- Of the `q_r` indices before the `r`th element of `Q`, precisely
`q_r-r` belong to the complement. This is the exponent occurring in the
paper's formula for epsilon. -/
private theorem paper_card_complement_before {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) (r : Fin n) :
    (Qᶜ.filter (fun x => x < Q.orderEmbOfFin hQ r)).card =
      (Q.orderEmbOfFin hQ r).val - r.val := by
  classical
  let q := Q.orderEmbOfFin hQ r
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.Iio q) (fun x => x ∈ Q)
  have hfirst : (Finset.Iio q).filter (fun x => x ∈ Q) =
      Q.filter (fun x => x < q) := by
    ext x
    simp [and_comm]
  have hsecond : (Finset.Iio q).filter (fun x => x ∉ Q) =
      Qᶜ.filter (fun x => x < q) := by
    ext x
    simp [and_comm]
  have hbefore : (Q.filter (fun x => x < q)).card = r.val := by
    simpa [q] using paper_card_Q_before Q hQ r
  rw [hfirst, hsecond, hbefore] at hsplit
  have hcard : (Finset.Iio q).card = q.val := by simp [q]
  rw [hcard] at hsplit
  change (Qᶜ.filter (fun x => x < q)).card = q.val - r.val
  omega

/-- The paper's normalization subset `Q₀={1,…,n}` has epsilon equal to 1.
Indices here are zero-based, so `Fin.castAdd k` lists its elements. -/
theorem paperEpsilon_firstCols {n k : ℕ} :
    paperEpsilon ((Finset.univ : Finset (Fin n)).map (Fin.castAddEmb k)) (by simp) = 1 := by
  let Q₀ := (Finset.univ : Finset (Fin n)).map (Fin.castAddEmb k)
  have hQ₀ : Q₀.card = n := by simp [Q₀]
  let e : Fin n ↪o Fin (n+k) := {
    toFun := Fin.castAdd k
    inj' := Fin.castAdd_injective n k
    map_rel_iff' := by intro i j; rfl }
  have he : e = Q₀.orderEmbOfFin hQ₀ := by
    apply Finset.orderEmbOfFin_unique' (h := hQ₀)
    intro i
    change Fin.castAdd k i ∈ Q₀
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  change (-1 : ℤˣ) ^
    (∑ r : Fin n, ((Q₀.orderEmbOfFin hQ₀ r).val - r.val)) = 1
  rw [← he]
  simp [e, Fin.castAdd]

/-- The paper's other normalization subset `H={k+1,…,k+n}` has epsilon
`(-1)^(nk)`. -/
private def paperLastRowsEmb (n k : ℕ) : Fin n ↪o Fin (n+k) := {
  toFun := fun i => ⟨k + i.val,
    by simpa [Nat.add_comm] using Nat.add_lt_add_left i.isLt k⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val h)
  map_rel_iff' := by
    intro a b
    change k + a.val ≤ k + b.val ↔ a.val ≤ b.val
    exact Nat.add_le_add_iff_left
}

theorem paperEpsilon_lastRows {n k : ℕ} :
    paperEpsilon (Finset.univ.map (paperLastRowsEmb n k).toEmbedding) (by simp) =
      (-1 : ℤˣ) ^ (n*k) := by
  let H := Finset.univ.map (paperLastRowsEmb n k).toEmbedding
  have hH : H.card = n := by simp [H]
  have he : paperLastRowsEmb n k = H.orderEmbOfFin hH := by
    apply Finset.orderEmbOfFin_unique' (h := hH)
    intro i
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  change (-1 : ℤˣ) ^
    (∑ r : Fin n, ((H.orderEmbOfFin hH r).val - r.val)) = _
  rw [← he]
  have hsum :
      (∑ r : Fin n, ((paperLastRowsEmb n k r).val - r.val)) = n*k := by
    change (∑ r : Fin n, (k + r.val - r.val)) = n*k
    simp [Finset.sum_const]
  rw [hsum]

private def paperFinsetSplitPermFin {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) : Equiv.Perm (Fin (k+n)) :=
  let e := finSumFinEquiv (m := k) (n := n)
  let s := (paperFinsetSplit Q hQ).trans (paperSplitRows n k).symm
  e.symm.trans (s.trans e)

private theorem paperFinsetSplitPermFin_left {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) (i : Fin k) :
    paperFinsetSplitPermFin Q hQ (Fin.castAdd n i) =
      Fin.cast (Nat.add_comm n k) (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ) i) := by
  simp [paperFinsetSplitPermFin, paperFinsetSplit, paperSplitRows,
    finSumEquivOfFinset_inl]

private theorem paperFinsetSplitPermFin_right {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) (i : Fin n) :
    paperFinsetSplitPermFin Q hQ (Fin.natAdd k i) =
      Fin.cast (Nat.add_comm n k) (Q.orderEmbOfFin hQ i) := by
  simp [paperFinsetSplitPermFin, paperFinsetSplit, paperSplitRows,
    finSumEquivOfFinset_inr]

private theorem paper_prod_ite_sign {k d : ℕ} (p : Fin k → Prop)
    [DecidablePred p]
    (hd : (Finset.univ.filter p).card = d) (hdk : d ≤ k) :
    (∏ i : Fin k, if p i then (1 : ℤˣ) else -1) = (-1)^(k+d) := by
  classical
  have hn : (Finset.univ.filter (fun i : Fin k => ¬ p i)).card = k-d := by
    have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ) p
    rw [hd, Finset.card_univ, Fintype.card_fin] at hs
    omega
  rw [show (∏ i : Fin k, if p i then (1 : ℤˣ) else -1) =
    ∏ i ∈ Finset.univ, if p i then (1 : ℤˣ) else -1 by simp]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, hn]
  have hpow : (-1 : ℤˣ)^(k-d) = (-1)^(k+d) := by
    have he : k-d+2*d = k+d := by omega
    calc
      (-1 : ℤˣ)^(k-d) = (-1)^(k-d) * 1 := by simp
      _ = (-1)^(k-d) * ((-1 : ℤˣ)^2)^d := by simp
      _ = (-1 : ℤˣ)^((k-d)+2*d) := by rw [pow_add, pow_mul]
      _ = (-1 : ℤˣ)^(k+d) := by rw [he]
  simpa using hpow

/-- The sign of the complementary shuffle is the explicit sign used in the
paper's Laplace expansion. The proof counts inversions by crossing pairs:
for each `q_r`, exactly `q_r-r` complementary indices precede it. -/
theorem paperFinsetSplit_sign_eq_paperEpsilon {n k : ℕ}
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) :
    Equiv.Perm.sign ((paperFinsetSplit Q hQ).trans (paperSplitRows n k).symm) =
      (-1 : ℤˣ)^(n*k) * paperEpsilon Q hQ := by
  classical
  let e := finSumFinEquiv (m := k) (n := n)
  let σ := (paperFinsetSplit Q hQ).trans (paperSplitRows n k).symm
  have hconj : e.symm.trans (σ.trans e) = paperFinsetSplitPermFin Q hQ := by
    rfl
  have hconj' : (e.symm.trans σ).trans e = paperFinsetSplitPermFin Q hQ := by
    rw [Equiv.trans_assoc]
    exact hconj
  have hsign : Equiv.Perm.sign σ =
      Equiv.Perm.sign (paperFinsetSplitPermFin Q hQ) := by
    rw [← Equiv.Perm.sign_symm_trans_trans σ e, hconj']
  rw [hsign, Equiv.Perm.sign_eq_prod_prod_Ioi]
  have hIoi (i : Fin (k+n)) : Finset.Ioi i = Finset.univ.filter (i < ·) := by
    ext j
    simp
  rw [show (∏ i : Fin (k+n), ∏ j ∈ Finset.Ioi i,
      (if paperFinsetSplitPermFin Q hQ i < paperFinsetSplitPermFin Q hQ j
        then (1 : ℤˣ) else -1)) =
    ∏ i : Fin (k+n), ∏ j : Fin (k+n),
      (if i < j then
        (if paperFinsetSplitPermFin Q hQ i < paperFinsetSplitPermFin Q hQ j
          then (1 : ℤˣ) else -1) else 1) by
        apply Finset.prod_congr rfl
        intro i _
        rw [hIoi i, Finset.prod_filter]]
  rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add]
  have hcross (i : Fin k) (r : Fin n) : i.val < k + r.val := by omega
  have hreverse (r : Fin n) (i : Fin k) : ¬ k + r.val < i.val := by omega
  have hwithinC (i j : Fin k) :
      (if i.val < j.val then
        if (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ) i).val <
          (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ) j).val then
            (1 : ℤˣ) else -1
        else 1) = 1 := by
    have hlt : (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ) i).val <
        (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ) j).val ↔ i.val < j.val := by
      simpa only [Fin.lt_def] using
        (Qᶜ.orderEmbOfFin (paper_complement_card Q hQ)).lt_iff_lt
    simp [hlt]
  have hwithinQ (i j : Fin n) :
      (if i.val < j.val then
        if (Q.orderEmbOfFin hQ i).val < (Q.orderEmbOfFin hQ j).val
          then (1 : ℤˣ) else -1
        else 1) = 1 := by
    have hlt : (Q.orderEmbOfFin hQ i).val < (Q.orderEmbOfFin hQ j).val ↔
        i.val < j.val := by
      simpa only [Fin.lt_def] using (Q.orderEmbOfFin hQ).lt_iff_lt
    simp [hlt]
  simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast,
    Nat.add_lt_add_iff_left, paperFinsetSplitPermFin_left,
    paperFinsetSplitPermFin_right]
  simp_rw [hwithinC, hwithinQ]
  simp [hcross, hreverse]
  let eC := Qᶜ.orderEmbOfFin (paper_complement_card Q hQ)
  let eQ := Q.orderEmbOfFin hQ
  have hsetC : Qᶜ = (Finset.univ : Finset (Fin k)).map eC.toEmbedding := by
    symm
    exact Finset.map_orderEmbOfFin_univ Qᶜ (paper_complement_card Q hQ)
  have hmapC (r : Fin n) :
      ((Finset.univ : Finset (Fin k)).filter (fun i => eC i < eQ r)).map
          eC.toEmbedding = Qᶜ.filter (fun x => x < eQ r) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hmem : eC i ∈ Qᶜ := by
        rw [hsetC]
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact ⟨hmem, hi⟩
    · rintro ⟨hx, hlt⟩
      have hxmap : x ∈ (Finset.univ : Finset (Fin k)).map eC.toEmbedding := by
        rw [← hsetC]
        exact hx
      rcases Finset.mem_map.mp hxmap with ⟨i, _, rfl⟩
      exact ⟨i, hlt, rfl⟩
  have hcrossCard (r : Fin n) :
      (Finset.univ.filter (fun i : Fin k => eC i < eQ r)).card =
        (eQ r).val - r.val := by
    calc
      (Finset.univ.filter (fun i : Fin k => eC i < eQ r)).card =
          (((Finset.univ.filter (fun i : Fin k => eC i < eQ r)).map
            eC.toEmbedding).card) := by rw [Finset.card_map]
      _ = (Qᶜ.filter (fun x => x < eQ r)).card := by rw [hmapC r]
      _ = (eQ r).val - r.val := paper_card_complement_before Q hQ r
  have hprod (r : Fin n) :
      (∏ i : Fin k, if eC i < eQ r then (1 : ℤˣ) else -1) =
        (-1 : ℤˣ) ^ (k + ((eQ r).val - r.val)) := by
    have hd := hcrossCard r
    have hdk : ((eQ r).val - r.val) ≤ k := by
      have hle := Finset.card_filter_le (Qᶜ) (fun x => x < eQ r)
      rw [paper_complement_card Q hQ] at hle
      rw [← paper_card_complement_before Q hQ r]
      exact hle
    simpa [eC, eQ] using
      (paper_prod_ite_sign (fun i : Fin k => eC i < eQ r) hd hdk)
  calc
    (∏ i : Fin k, ∏ r : Fin n,
      if eC i < eQ r then (1 : ℤˣ) else -1) =
        ∏ r : Fin n, ∏ i : Fin k,
          if eC i < eQ r then (1 : ℤˣ) else -1 := Finset.prod_comm
    _ = ∏ r : Fin n, (-1 : ℤˣ) ^ (k + ((eQ r).val-r.val)) := by
      apply Finset.prod_congr rfl
      intro r _
      exact hprod r
    _ = (-1 : ℤˣ) ^ (n*k +
        ∑ r : Fin n, ((eQ r).val-r.val)) := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simp [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin]
    _ = (-1 : ℤˣ)^(n*k) *
        (-1 : ℤˣ)^(∑ r : Fin n, ((eQ r).val-r.val)) := by rw [pow_add]
    _ = _ := by simp [paperEpsilon, eQ]

theorem paper_XU_finset_complement_relation
    {F : Type*} [Field F] {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (U : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0)
    (hXQ0 : (firstCols X).det ≠ 0)
    (hUJ : (tailRowsAfterN U).det ≠ 0)
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) :
    (Matrix.of fun i j => X i (Q.orderEmbOfFin hQ j)).det *
        ((-1:F)^(n*k) * (tailRowsAfterN U).det) =
      (firstCols X).det *
        (((Equiv.Perm.sign
          ((paperFinsetSplit Q hQ).trans (paperSplitRows n k).symm) : ℤ) : F) *
          (U.submatrix (fun i : Fin k => Qᶜ.orderEmbOfFin
            (paper_complement_card Q hQ) i) id).det) := by
  classical
  let hQc := paper_complement_card Q hQ
  let pQ := paperFinsetSplit Q hQ
  have h := paper_XU_standard_complement_relation X U hXU hXQ0 hUJ pQ
  have hX : (Matrix.of fun i j => X i (pQ (Sum.inr j))).det =
      (Matrix.of fun i j => X i (Q.orderEmbOfFin hQ j)).det := by
    congr 1
    ext i j
    simp [pQ, paperFinsetSplit, finSumEquivOfFinset_inr]
  have hU : U.submatrix (fun i : Fin k => pQ (Sum.inl i)) id =
      U.submatrix (fun i : Fin k => Qᶜ.orderEmbOfFin hQc i) id := by
    ext i j
    simp [pQ, paperFinsetSplit, finSumEquivOfFinset_inl]
  rw [hX, hU] at h
  exact h

/-- The Y/Z complementary-minor relation for an arbitrary ordered subset Q. -/
theorem paper_YZ_finset_complement_relation
    {F : Type*} [Field F] {n k : ℕ}
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (Z : Matrix (Fin (n+k)) (Fin k) F)
    (hYTZ : Y.transpose * Z = 0)
    (hYH : (lastRowsY Y).det ≠ 0)
    (hZI : (firstRowsZ Z).det ≠ 0)
    (Q : Finset (Fin (n+k))) (hQ : Q.card = n) :
    (Matrix.of fun i j => Y (Q.orderEmbOfFin hQ i) j).det * (firstRowsZ Z).det =
      (lastRowsY Y).det *
        (((Equiv.Perm.sign
          ((paperFinsetSplit Q hQ).trans (paperSplitRows n k).symm) : ℤ) : F) *
          (Z.submatrix (fun i : Fin k => Qᶜ.orderEmbOfFin
            (paper_complement_card Q hQ) i) id).det) := by
  classical
  let hQc := paper_complement_card Q hQ
  let pQ := paperFinsetSplit Q hQ
  have h := paper_YZ_standard_complement_relation Y Z hYTZ hYH hZI pQ
  have hY : (Matrix.of fun i j => Y (pQ (Sum.inr i)) j).det =
      (Matrix.of fun i j => Y (Q.orderEmbOfFin hQ i) j).det := by
    congr 1
    ext i j
    simp [pQ, paperFinsetSplit, finSumEquivOfFinset_inr]
  have hZ : Z.submatrix (fun i : Fin k => pQ (Sum.inl i)) id =
      Z.submatrix (fun i : Fin k => Qᶜ.orderEmbOfFin hQc i) id := by
    ext i j
    simp [pQ, paperFinsetSplit, finSumEquivOfFinset_inl]
  rw [hY, hZ] at h
  exact h

end AffineDualJT
