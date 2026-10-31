import AffineDualJT.Coefficients

/-!
# Basic coefficient data

Formalization target: pp.1--2 and §3.2 of the paper.

We keep the coefficient sequence abstract at first.  This isolates the purely
linear-algebraic/folding arguments from the concrete implementation of
`Ė(u)=∏(1+ux_a)(1+ux_a⁻¹)`.
-/

namespace AffineDualJT

open scoped BigOperators
noncomputable section

/-- Convert a zero-based Lean `Fin` index to the one-based integer index used in the paper. -/
def paperIndex {k : ℕ} (i : Fin k) : ℤ := (i.1 : ℤ) + 1

@[simp] theorem paperIndex_eq {k : ℕ} (i : Fin k) :
    paperIndex i = (i.1 : ℤ) + 1 := rfl

theorem paperIndex_pos {k : ℕ} (i : Fin k) : 0 < paperIndex i := by
  simp [paperIndex]

theorem paperIndex_le {k : ℕ} (i : Fin k) : paperIndex i ≤ (k : ℤ) := by
  simp only [paperIndex]
  omega

section Kernels
variable {R : Type*} [CommRing R]
variable {n k : ℕ}

/-- Paper p.1: `Λ_i(m)=ė_{n-i+m}-ė_{n+i+m}`. -/
def lambdaKernel (c : CoeffSystem R n) (i : Fin k) (m : ℤ) : R :=
  c.eDot ((n : ℤ) - paperIndex i + m) -
    c.eDot ((n : ℤ) + paperIndex i + m)

/-- Paper p.1: `h_i(m)=ė_{n-i+m}+ė_{n+i+m-1}`. -/
def hKernel (c : CoeffSystem R n) (i : Fin k) (m : ℤ) : R :=
  c.eDot ((n : ℤ) - paperIndex i + m) +
    c.eDot ((n : ℤ) + paperIndex i + m - 1)

/-- Paper p.1: `h_i⁺(m)=ė_{n-i+m}+ė_{n+i+m-2}`. -/
def hPlusKernel (c : CoeffSystem R n) (i : Fin k) (m : ℤ) : R :=
  c.eDot ((n : ℤ) - paperIndex i + m) +
    c.eDot ((n : ℤ) + paperIndex i + m - 2)

/-- Paper p.2 / §5.3: `ĥ_i(m)` formed with `ë`. -/
def hHatKernel (c : CoeffSystem R n) (i : Fin k) (m : ℤ) : R :=
  c.eDdot ((n : ℤ) - paperIndex i + m) +
    c.eDdot ((n : ℤ) + paperIndex i + m - 1)

/-- Paper p.7, equation (3.2): `Λ_i(-m)=-Λ_i(m)`. -/
theorem lambdaKernel_neg (c : CoeffSystem R n) (i : Fin k) (m : ℤ) :
    lambdaKernel c i (-m) = - lambdaKernel c i m := by
  have h₁ :
      c.eDot ((n : ℤ) - paperIndex i - m) =
        c.eDot ((n : ℤ) + paperIndex i + m) := by
    rw [← c.eDot_pal ((n : ℤ) + paperIndex i + m)]
    congr 1
    ring
  have h₂ :
      c.eDot ((n : ℤ) + paperIndex i - m) =
        c.eDot ((n : ℤ) - paperIndex i + m) := by
    rw [← c.eDot_pal ((n : ℤ) - paperIndex i + m)]
    congr 1
    ring
  simp only [lambdaKernel, ← sub_eq_add_neg]
  rw [h₁, h₂]
  ring

/-- The zero index is omitted in the odd folding in Lemmas 3.2 and 3.3. -/
@[simp] theorem lambdaKernel_zero (c : CoeffSystem R n) (i : Fin k) :
    lambdaKernel c i 0 = 0 := by
  unfold lambdaKernel
  have he := c.eDot_pal ((n : ℤ) + paperIndex i)
  rw [show 2 * (n : ℤ) - ((n : ℤ) + paperIndex i) = (n : ℤ) - paperIndex i by ring] at he
  simpa using sub_eq_zero.mpr he

/-- Paper p.7, equation (3.2): `h_i(1-m)=h_i(m)`. -/
theorem hKernel_reflect (c : CoeffSystem R n) (i : Fin k) (m : ℤ) :
    hKernel c i (1 - m) = hKernel c i m := by
  have h₁ :
      c.eDot ((n : ℤ) - paperIndex i + (1 - m)) =
        c.eDot ((n : ℤ) + paperIndex i + m - 1) := by
    rw [← c.eDot_pal ((n : ℤ) + paperIndex i + m - 1)]
    congr 1
    ring
  have h₂ :
      c.eDot ((n : ℤ) + paperIndex i + (1 - m) - 1) =
        c.eDot ((n : ℤ) - paperIndex i + m) := by
    rw [← c.eDot_pal ((n : ℤ) - paperIndex i + m)]
    congr 1
    ring
  simp only [hKernel]
  rw [h₁, h₂]
  ring

/-- Paper p.7, equation (3.2): `h_i⁺(2-m)=h_i⁺(m)`. -/
theorem hPlusKernel_reflect (c : CoeffSystem R n) (i : Fin k) (m : ℤ) :
    hPlusKernel c i (2 - m) = hPlusKernel c i m := by
  have h₁ :
      c.eDot ((n : ℤ) - paperIndex i + (2 - m)) =
        c.eDot ((n : ℤ) + paperIndex i + m - 2) := by
    rw [← c.eDot_pal ((n : ℤ) + paperIndex i + m - 2)]
    congr 1
    ring
  have h₂ :
      c.eDot ((n : ℤ) + paperIndex i + (2 - m) - 2) =
        c.eDot ((n : ℤ) - paperIndex i + m) := by
    rw [← c.eDot_pal ((n : ℤ) - paperIndex i + m)]
    congr 1
    ring
  simp only [hPlusKernel]
  rw [h₁, h₂]
  ring

/-- Paper p.12, §5.3: `ĥ_i(m)=h_i(m)+h_i(m-1)`. -/
theorem hHat_eq_h_add_shift (c : CoeffSystem R n) (i : Fin k) (m : ℤ) :
    hHatKernel c i m = hKernel c i m + hKernel c i (m - 1) := by
  simp only [hHatKernel, hKernel, c.eDdot_eq]
  have hs : (n : ℤ) - paperIndex i + m - 1 = (n : ℤ) - paperIndex i + (m - 1) := by ring
  have ht : (n : ℤ) + paperIndex i + m - 1 - 1 =
      (n : ℤ) + paperIndex i + (m - 1) - 1 := by ring
  rw [hs, ht]
  ring

/-- §3.2: the positive part of the coefficient kernels ends at `L=n+k`. -/
theorem lambdaKernel_zero_of_gt (c : CoeffSystem R n) (i : Fin k) (m : ℤ)
    (hm : (n : ℤ) + k < m) : lambdaKernel c i m = 0 := by
  have hi := paperIndex_le i
  have hi0 := paperIndex_pos i
  rw [lambdaKernel, c.eDot_zero_of_gt _ (by omega), c.eDot_zero_of_gt _ (by omega)]
  simp

theorem hKernel_zero_of_gt (c : CoeffSystem R n) (i : Fin k) (m : ℤ)
    (hm : (n : ℤ) + k < m) : hKernel c i m = 0 := by
  have hi := paperIndex_le i
  have hi0 := paperIndex_pos i
  rw [hKernel, c.eDot_zero_of_gt _ (by omega), c.eDot_zero_of_gt _ (by omega)]
  simp

theorem hPlusKernel_zero_of_gt (c : CoeffSystem R n) (i : Fin k) (m : ℤ)
    (hm : (n : ℤ) + k < m) : hPlusKernel c i m = 0 := by
  have hi := paperIndex_le i
  have hi0 := paperIndex_pos i
  rw [hPlusKernel, c.eDot_zero_of_gt _ (by omega), c.eDot_zero_of_gt _ (by omega)]
  simp

/-- Finite support is proved independently of the eventual residue weights. -/
theorem lambdaKernel_hasFiniteSupport (c : CoeffSystem R n) (i : Fin k) :
    Function.HasFiniteSupport (lambdaKernel c i) := by
  unfold lambdaKernel
  apply Function.HasFiniteSupport.sub
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)

theorem hKernel_hasFiniteSupport (c : CoeffSystem R n) (i : Fin k) :
    Function.HasFiniteSupport (hKernel c i) := by
  unfold hKernel
  apply Function.HasFiniteSupport.add
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)

theorem hPlusKernel_hasFiniteSupport (c : CoeffSystem R n) (i : Fin k) :
    Function.HasFiniteSupport (hPlusKernel c i) := by
  unfold hPlusKernel
  apply Function.HasFiniteSupport.add
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)
  · exact c.eDot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)

theorem hHatKernel_hasFiniteSupport (c : CoeffSystem R n) (i : Fin k) :
    Function.HasFiniteSupport (hHatKernel c i) := by
  unfold hHatKernel
  apply Function.HasFiniteSupport.add
  · exact c.eDdot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)
  · exact c.eDdot_hasFiniteSupport.fun_comp_of_injective (by intro a b h; dsimp at h; omega)

end Kernels
end
end AffineDualJT
