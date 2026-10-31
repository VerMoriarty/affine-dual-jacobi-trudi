import AffineDualJT.Basic

/-!
# Finite unfolding of integer sequences

Pairing `m` with `-m`, `1-m`, or `2-m` gives the three unfoldings in
Lemma 3.3. We prove the exact support inclusion in finite index sets
before splitting the sums. The third unfolding counts the fixed index
`m=1` once.
-/
open scoped BigOperators
namespace AffineDualJT
noncomputable section
private def positiveRows (L : ℕ) : Finset ℤ := Finset.univ.image (@paperIndex L)
private theorem paperIndex_injective {L : ℕ} : Function.Injective (@paperIndex L) := by
  intro i j h
  apply Fin.ext
  simp only [paperIndex] at h
  omega
private theorem mem_positiveRows {L : ℕ} (m : ℤ) :
    m ∈ positiveRows L ↔ 1 ≤ m ∧ m ≤ L := by
  constructor
  · intro hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨by have := paperIndex_pos i; omega, paperIndex_le i⟩
  · intro hm
    refine Finset.mem_image.mpr ⟨⟨(m-1).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only [paperIndex]
    omega
private theorem pair_finsum {F : Type*} [Field F] (S : Finset ℤ) (ρ : ℤ → ℤ)
    (hρ : Function.Injective ρ) (hd : Disjoint S (S.image ρ)) (f : ℤ → F)
    (hfs : Function.support f ⊆ ↑(S ∪ S.image ρ)) :
    (∑ᶠ m, f m) = ∑ m ∈ S, (f m+f (ρ m)) := by
  rw [finsum_eq_finsetSum_of_support_subset f hfs, Finset.sum_union hd,
    Finset.sum_image (by intro a ha b hb h; exact hρ h), ← Finset.sum_add_distrib]

theorem unfold_odd {F : Type*} [Field F] (L : ℕ) (f b : ℤ → F)
    (hzero : f 0 = 0) (hreflect : ∀ m, f (-m) = -f m)
    (hbound : ∀ m, (L : ℤ) < m → f m = 0) :
    (∑ᶠ m, f m * b m) =
      ∑ p : Fin L, f (paperIndex p) * (b (paperIndex p)-b (-paperIndex p)) := by
  have hd : Disjoint (positiveRows L) ((positiveRows L).image (fun m => -m)) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hm'
    have h₁ := (mem_positiveRows m).mp hm
    have h₂ := (mem_positiveRows r).mp hr
    omega
  have hfs : Function.support (fun m => f m * b m) ⊆
      ↑(positiveRows L ∪ (positiveRows L).image (fun m => -m)) := by
    intro m hm
    have hf : f m ≠ 0 := left_ne_zero_of_mul hm
    by_cases hp : 0 < m
    · apply Finset.mem_union_left
      apply (mem_positiveRows m).mpr
      constructor
      · omega
      · by_contra hh
        exact hf (hbound m (by omega))
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨-m, ?_, by ring⟩
      apply (mem_positiveRows (-m)).mpr
      have hmzero : m ≠ 0 := by intro h; subst m; exact hf hzero
      constructor
      · omega
      · by_contra hh
        have hfm := hreflect (-m)
        rw [neg_neg, hbound (-m) (by omega), neg_zero] at hfm
        exact hf hfm
  rw [pair_finsum (positiveRows L) (fun m => -m) neg_injective hd _ hfs]
  rw [positiveRows, Finset.sum_image (by intro a ha b hb h; exact paperIndex_injective h)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hreflect]
  ring

theorem unfold_center_one {F : Type*} [Field F] (L : ℕ) (f b : ℤ → F)
    (hreflect : ∀ m, f (1-m) = f m) (hbound : ∀ m, (L : ℤ) < m → f m = 0) :
    (∑ᶠ m, f m * b m) =
      ∑ p : Fin L, f (paperIndex p) * (b (paperIndex p)+b (1-paperIndex p)) := by
  have hd : Disjoint (positiveRows L) ((positiveRows L).image (fun m => 1-m)) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hm'
    have h₁ := (mem_positiveRows m).mp hm
    have h₂ := (mem_positiveRows r).mp hr
    omega
  have hfs : Function.support (fun m => f m * b m) ⊆
      ↑(positiveRows L ∪ (positiveRows L).image (fun m => 1-m)) := by
    intro m hm
    have hf : f m ≠ 0 := left_ne_zero_of_mul hm
    by_cases hp : 0 < m
    · apply Finset.mem_union_left
      apply (mem_positiveRows m).mpr
      constructor
      · omega
      · by_contra hh
        exact hf (hbound m (by omega))
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨1-m, ?_, by ring⟩
      apply (mem_positiveRows (1-m)).mpr
      constructor
      · omega
      · by_contra hh
        have hfm := hreflect (1-m)
        rw [show 1-(1-m)=m by ring, hbound (1-m) (by omega)] at hfm
        exact hf hfm
  rw [pair_finsum (positiveRows L) (fun m => 1-m) (by intro a b h; dsimp at h; omega) hd _ hfs]
  rw [positiveRows, Finset.sum_image (by intro a ha b hb h; exact paperIndex_injective h)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hreflect]
  ring
end
end AffineDualJT

namespace AffineDualJT
open scoped BigOperators
noncomputable section
theorem unfold_center_two {F : Type*} [Field F] (L : ℕ) (hL : 0 < L)
    (f b : ℤ → F) (hreflect : ∀ m, f (2-m) = f m)
    (hbound : ∀ m, (L : ℤ) < m → f m = 0) :
    (∑ᶠ m, f m * b m) = ∑ p : Fin L,
      if p.val = 0 then f 1 * b 1 else
        f (paperIndex p) * (b (paperIndex p)+b (2-paperIndex p)) := by
  have hmem : ∀ m : ℤ, m ∈ (positiveRows L).image (fun r => 2-r) ↔
      2-(L:ℤ) ≤ m ∧ m ≤ 1 := by
    intro m
    constructor
    · intro hm
      obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hm
      have h := (mem_positiveRows r).mp hr
      omega
    · intro hm
      exact Finset.mem_image.mpr ⟨2-m, (mem_positiveRows _).mpr (by omega), by ring⟩
  have hi : positiveRows L ∩ (positiveRows L).image (fun m => 2-m) = {1} := by
    ext m
    simp only [Finset.mem_inter, mem_positiveRows, hmem, Finset.mem_singleton]
    omega
  have hfs : Function.support (fun m => f m * b m) ⊆
      ↑(positiveRows L ∪ (positiveRows L).image (fun m => 2-m)) := by
    intro m hm
    have hf : f m ≠ 0 := left_ne_zero_of_mul hm
    by_cases hp : 0 < m
    · apply Finset.mem_union_left
      apply (mem_positiveRows m).mpr
      constructor
      · omega
      · by_contra hh
        exact hf (hbound m (by omega))
    · apply Finset.mem_union_right
      apply (hmem m).mpr
      constructor
      · by_contra hh
        have hfm := hreflect (2-m)
        rw [show 2-(2-m)=m by ring, hbound (2-m) (by omega)] at hfm
        exact hf hfm
      · omega
  rw [finsum_eq_finsetSum_of_support_subset _ hfs]
  have hs := Finset.sum_union_inter (f := fun m => f m * b m)
    (s₁ := positiveRows L) (s₂ := (positiveRows L).image (fun m => 2-m))
  rw [hi, Finset.sum_singleton,
    Finset.sum_image (by intro a ha b hb h; dsimp at h; omega), ← Finset.sum_add_distrib,
    positiveRows, Finset.sum_image (by intro a ha b hb h; exact paperIndex_injective h)] at hs
  have he : (∑ p : Fin L, (f (paperIndex p)*b (paperIndex p)+
      f (2-paperIndex p)*b (2-paperIndex p))) =
      (∑ p : Fin L, if p.val = 0 then f 1*b 1 else
        f (paperIndex p)*(b (paperIndex p)+b (2-paperIndex p))) + f 1*b 1 := by
    have hp : ∀ p : Fin L, f (paperIndex p)*b (paperIndex p)+
        f (2-paperIndex p)*b (2-paperIndex p) =
        (if p.val = 0 then f 1*b 1 else
          f (paperIndex p)*(b (paperIndex p)+b (2-paperIndex p))) +
            (if p = ⟨0,hL⟩ then f 1*b 1 else 0) := by
      intro p
      rw [hreflect]
      by_cases h : p.val = 0
      · have hp : p = ⟨0,hL⟩ := Fin.ext h
        simp [hp, paperIndex]
      · have hp : p ≠ ⟨0,hL⟩ := by intro he; exact h (congrArg Fin.val he)
        simp only [h, hp, ite_false, add_zero]
        ring
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    simp
  rw [he] at hs
  exact add_right_cancel hs
end
end AffineDualJT
