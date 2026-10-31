import AffineDualJT.Kernels
import AffineDualJT.AffineDetSum
import AffineDualJT.FiniteUnfolding
import AffineDualJT.DeterminantFinsum

/-! # Folding and finite unfolding (§3.3, equation (3.4), Lemma 3.3). -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Definitions
variable {F : Type*} [Field F]
variable {n k : ℕ}

def CC (b : Fin k → ℤ → F) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p j => b j (paperIndex p) - b j (-paperIndex p)

def CB (b : Fin k → ℤ → F) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p j => (-1:F)^(p.1+1) * (b j (paperIndex p) + b j (1-paperIndex p))

def CPlus (b : Fin k → ℤ → F) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p j => if p.1=0 then -b j 1 else
    (-1:F)^(p.1+1) * (b j (paperIndex p) + b j (2-paperIndex p))
end Definitions

section Lemma33
variable {F : Type*} [Field F]
variable {n k : ℕ}
variable (c : CoeffSystem F n)

/-- Lemma 3.3, equation (3.5). -/
theorem lemma_3_3_eq_3_5 (b : Fin k → ℤ → F) (i j : Fin k) :
    ((DC (k:=k) c).transpose * CC (n:=n) b) i j =
      ∑ᶠ m : ℤ, ((-1:F)^m) * lambdaKernel c i m * b j m := by
  have hzero : lambdaKernel c i 0 = 0 := by
    unfold lambdaKernel
    have he := c.eDot_pal ((n:ℤ)+paperIndex i)
    rw [show 2*(n:ℤ)-((n:ℤ)+paperIndex i) = (n:ℤ)-paperIndex i by ring] at he
    simpa using sub_eq_zero.mpr he
  have h := unfold_odd (n+k) (lambdaKernel c i) (fun m => (-1:F)^m * b j m)
    hzero (lambdaKernel_neg c i) (fun m hm => lambdaKernel_zero_of_gt c i m (by
      simpa using hm))
  have hs : ∀ m : ℤ, (-1:F)^(-m) = (-1:F)^m := by
    intro m
    simp only [← Int.cast_negOnePow F, Int.negOnePow_neg]
  have he : (∑ᶠ m : ℤ, lambdaKernel c i m * ((-1:F)^m * b j m)) =
      ∑ᶠ m : ℤ, (-1:F)^m * lambdaKernel c i m * b j m := by
    apply finsum_congr
    intro m
    ring
  rw [← he, h, mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hs]
  have hsn : (-1:F)^(paperIndex p) = (-1:F)^(p.val+1) := by
    rw [show paperIndex p = ((p.val+1:ℕ):ℤ) by simp [paperIndex], zpow_natCast]
  rw [hsn]
  simp only [DC, CC, transpose_apply, rowSign]
  ring

/-- Lemma 3.3, equation (3.6). -/
theorem lemma_3_3_eq_3_6 (b : Fin k → ℤ → F) (i j : Fin k) :
    ((DB (k:=k) c).transpose * CB (n:=n) b) i j =
      ∑ᶠ m : ℤ, hKernel c i m * b j m := by
  rw [unfold_center_one (n+k) (hKernel c i) (b j) (hKernel_reflect c i)
    (fun m hm => hKernel_zero_of_gt c i m (by simpa using hm)), mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [DB, CB, transpose_apply, rowSign]
  have hs : (-1:F)^(p.val+1) * (-1:F)^(p.val+1) = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul _).neg_one_pow
  calc
    _ = ((-1:F)^(p.val+1) * (-1:F)^(p.val+1)) *
      (hKernel c i (paperIndex p) * (b j (paperIndex p)+b j (1-paperIndex p))) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Lemma 3.3, equation (3.7). -/
theorem lemma_3_3_eq_3_7 (b : Fin k → ℤ → F) (i j : Fin k) :
    ((DPlus (k:=k) c).transpose * CPlus (n:=n) b) i j =
      ∑ᶠ m : ℤ, hPlusKernel c i m * b j m := by
  have hL : 0 < n+k := by have := i.isLt; omega
  rw [unfold_center_two (n+k) hL (hPlusKernel c i) (b j) (hPlusKernel_reflect c i)
    (fun m hm => hPlusKernel_zero_of_gt c i m (by simpa using hm)), mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [DPlus, CPlus, transpose_apply, rowSign]
  by_cases hz : p.val = 0
  · simp [hz, paperIndex]
  · simp only [hz, ite_false]
    have hs : (-1:F)^(p.val+1) * (-1:F)^(p.val+1) = 1 := by
      rw [← pow_add, ← two_mul]
      exact (even_two_mul _).neg_one_pow
    calc
      _ = ((-1:F)^(p.val+1) * (-1:F)^(p.val+1)) *
        (hPlusKernel c i (paperIndex p) * (b j (paperIndex p)+b j (2-paperIndex p))) := by ring
      _ = _ := by rw [hs, one_mul]

/--
p.8, support bound: below the lower `y` threshold both coefficient indices
are above the support interval `[0,N]`.

This is the inequality form underlying the displayed ceiling bound in the
paper; it avoids committing the formalization to a particular integer
ceiling API.
-/
theorem row_zero_below_support
    (E : ℤ → F) (N K : ℤ) (_hK : 0<K)
    (hEhi : ∀ r, N<r → E r=0)
    (i j : Fin k) (σ : F) (δ y : ℤ)
    (hδ : δ ≤ 2*paperIndex i)
    (hy : K*y < (n:ℤ)-paperIndex i+1-N) :
    E ((n:ℤ)-paperIndex i+paperIndex j-K*y) +
      σ * E ((n:ℤ)+paperIndex i+paperIndex j-K*y-δ) = 0 := by
  have hj : 1 ≤ paperIndex j := by
    simp [paperIndex]
  have hA : N < (n:ℤ)-paperIndex i+paperIndex j-K*y := by
    omega
  have hB : N < (n:ℤ)+paperIndex i+paperIndex j-K*y-δ := by
    omega
  rw [hEhi _ hA, hEhi _ hB]
  simp

/--
p.8, support bound: above the upper `y` threshold both coefficient indices
are negative.  Together with `row_zero_below_support` this gives finite row
support and hence justifies finite multilinearity.
-/
theorem row_zero_above_support
    (E : ℤ → F) (K : ℤ) (_hK : 0<K)
    (hElo : ∀ r, r<0 → E r=0)
    (i j : Fin k) (σ : F) (δ y : ℤ)
    (hδ : δ ≤ 2*paperIndex i)
    (hy : (n:ℤ)+paperIndex i+(k:ℤ)-δ < K*y) :
    E ((n:ℤ)-paperIndex i+paperIndex j-K*y) +
      σ * E ((n:ℤ)+paperIndex i+paperIndex j-K*y-δ) = 0 := by
  have hjk : paperIndex j ≤ (k:ℤ) := by
    simp only [paperIndex]
    omega
  have hB : (n:ℤ)+paperIndex i+paperIndex j-K*y-δ < 0 := by
    omega
  have hA : (n:ℤ)-paperIndex i+paperIndex j-K*y < 0 := by
    omega
  rw [hElo _ hA, hElo _ hB]
  simp

end Lemma33
end
end AffineDualJT
