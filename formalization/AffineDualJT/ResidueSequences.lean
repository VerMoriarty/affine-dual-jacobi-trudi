import AffineDualJT.Basic

/-!
# Finite residue-class reindexing and affine fold reflections

The sums defining the §4–§5 residue sequences contain at most one nonzero
term when the period is nonzero.  The reindexing identities below also hold
for arbitrary periods with mathlib's `finsum` convention.  They implement the
integer shifts used in the paper's proofs of (4.1), (4.2), and (5.2).
-/
open scoped BigOperators
namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F]
def residueSum (K j : ℤ) (w : ℤ → F) (m : ℤ) : F :=
  ∑ᶠ q : ℤ, if m = j + K*q then w q else 0

theorem residue_point_hasFiniteSupport (K j m : ℤ) (hK : K ≠ 0) (w : ℤ → F) :
    Function.HasFiniteSupport (fun q => if m = j+K*q then w q else 0) := by
  by_cases hex : ∃ q : ℤ, m = j+K*q
  · obtain ⟨q₀,hq₀⟩ := hex
    apply (Set.finite_singleton q₀).subset
    intro q hq
    change q = q₀
    have he : m = j+K*q := by
      by_contra h
      have hn : (if m = j+K*q then w q else 0) ≠ 0 := hq
      exact hn (by simp [h])
    apply mul_left_cancel₀ hK
    linear_combination hq₀-he
  · have hs : Function.support (fun q => if m = j+K*q then w q else 0) = ∅ := by
      ext q
      simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false]
      have h : ¬m=j+K*q := by intro h; exact hex ⟨q,h⟩
      simp [h]
    rw [Function.HasFiniteSupport, hs]
    exact Set.finite_empty

theorem residue_point_eq (K j : ℤ) (hK : K ≠ 0) (w : ℤ → F) (q₀ : ℤ) :
    residueSum K j w (j+K*q₀) = w q₀ := by
  unfold residueSum
  rw [finsum_eq_single _ q₀]
  · simp
  · intro q hq
    have h : ¬j+K*q₀=j+K*q := by
      intro h
      apply hq
      apply mul_left_cancel₀ hK
      linear_combination -h
    simp [h]

theorem residueSum_quasiperiod (K j : ℤ) (w : ℤ → F) (a : ℤ → F)
    (hw : ∀ q, w (q+1) = a (j+K*q) * w q) (m : ℤ) :
    residueSum K j w (m+K) = a m * residueSum K j w m := by
  unfold residueSum
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ)), mul_finsum]
  apply finsum_congr
  intro q
  change (if m+K = j+K*(q+1) then w (q+1) else 0) =
    a m * (if m = j+K*q then w q else 0)
  by_cases h : m = j+K*q
  · have h' : m+K = j+K*(q+1) := by rw [h]; ring
    rw [ite_eq_left h', ite_eq_left h, hw, h]
  · have h' : ¬m+K = j+K*(q+1) := by
      intro hh
      apply h
      linear_combination hh
    simp [h, h']
end
end AffineDualJT

namespace AffineDualJT
noncomputable section
variable {F : Type*} [Field F]
theorem residueSum_minus_quasiperiod (K j : ℤ) (w : ℤ → F) (a : ℤ → F)
    (hw : ∀ y, w (y-1) = a (j-K*y) * w y) (m : ℤ) :
    (∑ᶠ y : ℤ, if m+K = j-K*y then w y else 0) =
      a m * (∑ᶠ y : ℤ, if m = j-K*y then w y else 0) := by
  rw [← finsum_comp_equiv (Equiv.addRight (-1 : ℤ)), mul_finsum]
  apply finsum_congr
  intro y
  change (if m+K = j-K*(y-1) then w (y-1) else 0) =
    a m * (if m = j-K*y then w y else 0)
  by_cases h : m = j-K*y
  · have h' : m+K = j-K*(y-1) := by rw [h]; ring
    rw [ite_eq_left h', ite_eq_left h, hw, h]
  · have h' : ¬m+K = j-K*(y-1) := by
      intro hh
      apply h
      linear_combination hh
    simp [h, h']

theorem odd_fold_affine (K : ℤ) (b a : ℤ → F)
    (hshift : ∀ m, b (m+K) = a m * b m) (m : ℤ)
    (ha : a (m-K) * a (-m) = 1) :
    b m - b (-m) = -a (m-K) * (b (K-m) - b (m-K)) := by
  have h₁ := hshift (m-K)
  have h₂ := hshift (-m)
  rw [sub_add_cancel] at h₁
  rw [show -m+K = K-m by ring] at h₂
  rw [h₁, h₂]
  calc
    _ = a (m-K) * b (m-K) - (a (m-K)*a (-m)) * b (-m) := by rw [ha]; ring
    _ = _ := by ring

theorem center_fold_affine (K δ : ℤ) (b a : ℤ → F)
    (hshift : ∀ m, b (m+K) = a m * b m) (m : ℤ)
    (ha : a (m-K) * a (δ-m) = 1) :
    (-1:F)^m * (b m + b (δ-m)) =
      (-1:F)^(K+δ) * a (m-K) *
        ((-1:F)^(K+δ-m) * (b (K+δ-m) + b (m-K))) := by
  have h₁ := hshift (m-K)
  have h₂ := hshift (δ-m)
  rw [sub_add_cancel] at h₁
  rw [show δ-m+K = K+δ-m by ring] at h₂
  have hs : (-1:F)^(K+δ) * (-1:F)^(K+δ-m) = (-1:F)^m := by
    rw [← Int.cast_negOnePow F, ← Int.cast_negOnePow F, ← Int.cast_negOnePow F]
    norm_cast
    rw [Int.negOnePow_sub, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [h₁, h₂]
  calc
    _ = (-1:F)^m * (a (m-K)*b (m-K) + (a (m-K)*a (δ-m))*b (δ-m)) := by
      rw [ha, one_mul]
    _ = _ := by rw [← hs]; ring
end
end AffineDualJT

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

/-- In the open interval of one period, only the zero shift can occur. -/
theorem residueSum_small (K j m : ℤ) (hK : 0<K) (w : ℤ → F)
    (hlo : -K < m-j) (hhi : m-j < K) :
    residueSum K j w m = if m=j then w 0 else 0 := by
  unfold residueSum
  rw [finsum_eq_single _ 0]
  · simp
  · intro q hq
    have hne : m≠j+K*q := by
      intro h
      by_cases hpos : 0 < q
      · have hq1 : 1≤q := by omega
        nlinarith
      · have hq1 : q≤ -1 := by omega
        nlinarith
    simp only [hne,ite_false]

end
end AffineDualJT

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

/-- A residue-class `finsum` vanishes away from its defining class. -/
theorem residueSum_zero (K j m : ℤ) (w : ℤ → F)
    (hm : ∀ q, m≠j+K*q) : residueSum K j w m=0 := by
  simp only [residueSum,hm,ite_false,finsum_zero]

/-- Reindex a pairing against a residue sequence by its unique shift. -/
theorem residueSum_pairing (K j : ℤ) (hK : K≠0) (H w : ℤ → F) :
    (∑ᶠ m : ℤ, H m*residueSum K j w m) =
      ∑ᶠ q : ℤ, H (j+K*q)*w q := by
  classical
  let f : ℤ → F := fun m => H m*residueSum K j w m
  have hinj : Function.Injective (fun q : ℤ => j+K*q) := by
    intro q r h
    apply mul_left_cancel₀ hK
    linear_combination h
  calc
    (∑ᶠ m : ℤ, f m) = ∑ᶠ m ∈ Set.range (fun q : ℤ => j+K*q), f m := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro m
      by_cases hm : m ∈ Set.range (fun q : ℤ => j+K*q)
      · simp only [Set.indicator_of_mem hm]
      · have hz : residueSum K j w m=0 := residueSum_zero K j m w
          (by intro q h; exact hm ⟨q,h.symm⟩)
        simp only [Set.indicator_of_notMem hm,f,hz,mul_zero]
    _ = ∑ᶠ q : ℤ, f (j+K*q) := finsum_mem_range hinj
    _ = _ := by
      apply finsum_congr
      intro q
      simp only [f,residue_point_eq K j hK w q]

/-- The same pairing with the paper's descending residue index `j-Ky`. -/
theorem residueSum_minus_pairing (K j : ℤ) (hK : K≠0) (H w : ℤ → F) :
    (∑ᶠ m : ℤ, H m*(∑ᶠ y : ℤ, if m=j-K*y then w y else 0)) =
      ∑ᶠ y : ℤ, H (j-K*y)*w y := by
  simpa only [residueSum,neg_mul,sub_eq_add_neg] using
    residueSum_pairing (-K) j (neg_ne_zero.mpr hK) H w

/-- Principal-interval evaluation for a descending residue sequence. -/
theorem residueSum_minus_small (K j m : ℤ) (hK : 0<K) (w : ℤ → F)
    (hlo : -K < m-j) (hhi : m-j < K) :
    (∑ᶠ y : ℤ, if m=j-K*y then w y else 0)=if m=j then w 0 else 0 := by
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  simpa only [residueSum,Equiv.neg_apply,mul_neg,sub_neg_eq_add,neg_zero] using
    residueSum_small K j m hK (fun q => w (-q)) hlo hhi

end
end AffineDualJT
