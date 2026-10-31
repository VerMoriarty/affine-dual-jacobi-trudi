import AffineDualJT.FiniteColumnMinors
import AffineDualJT.Folding
import AffineDualJT.ResidueSequences

/-!
# Residue sequences and reflections for the four ordinary affine kernels (§4)

The identities themselves are assembled in `Section4Ordinary`; this module
contains the sequence definitions and their two reflection relations.

Important formalization point: the square-root cases are encoded in the
parameter `τ` directly.  We do **not** implement `t^(r/2)` by integer division,
since the paper explicitly defines `t^(r/2):=τ^r` in those cases (p.2).
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix
open AffineDetSum
noncomputable section

section C0Sequence
variable {F : Type*} [Field F]
variable {k : ℕ}

/-- §4.1, C0 case: `K=2k+2`, hence `Kq²/2=(k+1)q²`. -/
def bC0Seq (t : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ q : ℤ, if m = paperIndex j + (2*(k:ℤ)+2)*q then
    t^(((k:ℤ)+1)*q^2 + paperIndex j*q) else 0

def cC0Seq (t : F) (j : Fin k) (m : ℤ) : F := bC0Seq t j m - bC0Seq t j (-m)

/-- Equation (4.1), first reflection, C0. -/
theorem cC0_neg (t : F) (j : Fin k) (m : ℤ) : cC0Seq t j (-m) = -cC0Seq t j m := by
  simp [cC0Seq]

/-- Integer-shift recurrence used in the affine reflection proof. -/
theorem bC0_quasiperiod (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    bC0Seq t j (m+(2*(k:ℤ)+2)) = t^(m+(k:ℤ)+1) * bC0Seq t j m := by
  apply residueSum_quasiperiod (2*(k:ℤ)+2) (paperIndex j)
    (fun q => t^(((k:ℤ)+1)*q^2+paperIndex j*q)) (fun m => t^(m+(k:ℤ)+1))
  intro q
  rw [← zpow_add₀ hparam]
  congr 1
  ring

/-- Equation (4.1), second reflection, specialized to `K=2k+2`. -/
theorem cC0_affine (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    cC0Seq t j m + t^(m-(k:ℤ)-1) * cC0Seq t j (2*(k:ℤ)+2-m) = 0 := by
  have ha : t^((m-(2*(k:ℤ)+2))+(k:ℤ)+1) * t^(-m+(k:ℤ)+1) = 1 := by
    rw [← zpow_add₀ hparam, show (m-(2*(k:ℤ)+2)+(k:ℤ)+1)+(-m+(k:ℤ)+1) = 0 by ring,
      zpow_zero]
  have h := odd_fold_affine (2*(k:ℤ)+2) (bC0Seq t j)
    (fun m => t^(m+(k:ℤ)+1)) (bC0_quasiperiod t hparam j) m ha
  have he : m-(2*(k:ℤ)+2)+(k:ℤ)+1 = m-(k:ℤ)-1 := by ring
  have hi : -(2*(k:ℤ)+2-m) = m-(2*(k:ℤ)+2) := by ring
  simp only [cC0Seq, hi]
  rw [h, he]
  ring

end C0Sequence

section BCSequence
variable {F : Type*} [Field F]
variable {k : ℕ}

/--
§4.1, BC case: `K=2k+1`, `t=τ²`.
The paper's `t^(Kq²/2+jq)` is exactly
`τ^(Kq²+2jq)`, avoiding half-integer powers in Lean.
-/
def bBCSeq (τ : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ q : ℤ, if m = paperIndex j + (2*(k:ℤ)+1)*q then
    τ^((2*(k:ℤ)+1)*q^2 + 2*paperIndex j*q) else 0

def cBCSeq (τ : F) (j : Fin k) (m : ℤ) : F := bBCSeq τ j m - bBCSeq τ j (-m)

/-- Odd reflection in the BC case. -/
theorem cBC_neg (τ : F) (j : Fin k) (m : ℤ) : cBCSeq τ j (-m) = -cBCSeq τ j m := by
  simp [cBCSeq]

/-- Integer-shift recurrence used in the affine reflection proof. -/
theorem bBC_quasiperiod (τ : F) (hparam : τ ≠ 0) (j : Fin k) (m : ℤ) :
    bBCSeq τ j (m+(2*(k:ℤ)+1)) = τ^(2*m+2*(k:ℤ)+1) * bBCSeq τ j m := by
  apply residueSum_quasiperiod (2*(k:ℤ)+1) (paperIndex j)
    (fun q => τ^((2*(k:ℤ)+1)*q^2+2*paperIndex j*q))
    (fun m => τ^(2*m+2*(k:ℤ)+1))
  intro q
  rw [← zpow_add₀ hparam]
  congr 1
  ring

/-- The second relation in (4.1), rewritten in `τ`. -/
theorem cBC_affine (τ : F) (hparam : τ ≠ 0) (j : Fin k) (m : ℤ) :
    cBCSeq τ j m + τ^(2*m-(2*(k:ℤ)+1)) * cBCSeq τ j (2*(k:ℤ)+1-m) = 0 := by
  have ha : τ^(2*(m-(2*(k:ℤ)+1))+2*(k:ℤ)+1) * τ^(2*(-m)+2*(k:ℤ)+1) = 1 := by
    rw [← zpow_add₀ hparam,
      show (2*(m-(2*(k:ℤ)+1))+2*(k:ℤ)+1)+(2*(-m)+2*(k:ℤ)+1) = 0 by ring,
      zpow_zero]
  have h := odd_fold_affine (2*(k:ℤ)+1) (bBCSeq τ j)
    (fun m => τ^(2*m+2*(k:ℤ)+1)) (bBC_quasiperiod τ hparam j) m ha
  have he : 2*(m-(2*(k:ℤ)+1))+2*(k:ℤ)+1 = 2*m-(2*(k:ℤ)+1) := by ring
  have hi : -(2*(k:ℤ)+1-m) = m-(2*(k:ℤ)+1) := by ring
  simp only [cBCSeq, hi]
  rw [h, he]
  ring

end BCSequence

section B0Sequence
variable {F : Type*} [Field F]
variable {k : ℕ}

/--
§4.2, B0 case, `K=2k+1`.
The exponent is kept as the *whole* even numerator divided by two:
`(K y²-(2j-1)y)/2`.  This is not split into two integer divisions.
Exactness and equality to the paper's rational exponent are certified by
`WeightExponents.B0_exponent_exact` and `B0_exponent_cast` (both in the
`AffineDualJT` namespace).
-/
def bB0Seq (t : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ y : ℤ, if m = paperIndex j - (2*(k:ℤ)+1)*y then
    (-1:F)^y * t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2) else 0

def gammaB0 (t : F) (j : Fin k) (m : ℤ) : F :=
  (-1:F)^m * (bB0Seq t j m + bB0Seq t j (1-m))

/-- Equation (4.2), first reflection, B0. -/
theorem gammaB0_first (t : F) (j : Fin k) (m : ℤ) :
    gammaB0 t j (1-m) = -gammaB0 t j m := by
  simp only [gammaB0, ← Int.cast_negOnePow F, Int.negOnePow_sub]
  norm_num
  ring
/-- Integer-shift recurrence used in the affine reflection proof. -/
theorem bB0_quasiperiod (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    bB0Seq t j (m+(2*(k:ℤ)+1)) = -t^(m+(k:ℤ)) * bB0Seq t j m := by
  apply residueSum_minus_quasiperiod (2*(k:ℤ)+1) (paperIndex j)
    (fun y => (-1:F)^y * t^(((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2))
    (fun m => -t^(m+(k:ℤ)))
  intro y
  rw [zpow_sub₀ (by norm_num : (-1:F) ≠ 0)]
  have he : ((2*(k:ℤ)+1)*(y-1)^2-(2*paperIndex j-1)*(y-1))/2 =
      (paperIndex j-(2*(k:ℤ)+1)*y+(k:ℤ))+
        ((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)/2 := by
    have hn : (2*(k:ℤ)+1)*(y-1)^2-(2*paperIndex j-1)*(y-1) =
        ((2*(k:ℤ)+1)*y^2-(2*paperIndex j-1)*y)+
          (paperIndex j-(2*(k:ℤ)+1)*y+(k:ℤ))*2 := by ring
    rw [hn, Int.add_mul_ediv_right]
    · ring
    · norm_num
  rw [he, zpow_add₀ hparam]
  norm_num
  ring

/-- Equation (4.2), second reflection, B0. -/
theorem gammaB0_second (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    gammaB0 t j m = -t^(m-(k:ℤ)-1) * gammaB0 t j (2*(k:ℤ)+2-m) := by
  have ha : (-t^((m-(2*(k:ℤ)+1))+(k:ℤ))) * (-t^(1-m+(k:ℤ))) = 1 := by
    rw [neg_mul_neg, ← zpow_add₀ hparam,
      show (m-(2*(k:ℤ)+1)+(k:ℤ))+(1-m+(k:ℤ)) = 0 by ring, zpow_zero]
  have h := center_fold_affine (2*(k:ℤ)+1) 1 (bB0Seq t j)
    (fun m => -t^(m+(k:ℤ))) (bB0_quasiperiod t hparam j) m ha
  have he : m-(2*(k:ℤ)+1)+(k:ℤ) = m-(k:ℤ)-1 := by ring
  have hi : 1-(2*(k:ℤ)+2-m) = m-(2*(k:ℤ)+1) := by ring
  have hc : 2*(k:ℤ)+1+1 = 2*(k:ℤ)+2 := by ring
  have hs : (-1:F)^(2*(k:ℤ)+2) = 1 := by
    rw [show 2*(k:ℤ)+2 = 2*((k:ℤ)+1) by ring]
    exact (even_two_mul _).neg_one_zpow
  simpa only [gammaB0, hc, he, hi, hs, one_mul] using h

end B0Sequence

section BminusSequence
variable {F : Type*} [Field F]
variable {k : ℕ}

/-- §4.2, `B-` case in the square-root parameter `τ`, `K=2k`. -/
def bBminusSeq (τ : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ y : ℤ, if m = paperIndex j - 2*(k:ℤ)*y then
    τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y) else 0

def gammaBminus (τ : F) (j : Fin k) (m : ℤ) : F :=
  (-1:F)^m * (bBminusSeq τ j m + bBminusSeq τ j (1-m))

/-- Equation (4.2), first reflection in the `B-` case. -/
theorem gammaBminus_first (τ : F) (j : Fin k) (m : ℤ) :
    gammaBminus τ j (1-m) = -gammaBminus τ j m := by
  simp only [gammaBminus, ← Int.cast_negOnePow F, Int.negOnePow_sub]
  norm_num
  ring
/-- Integer-shift recurrence used in the affine reflection proof. -/
theorem bBminus_quasiperiod (τ : F) (hparam : τ ≠ 0) (j : Fin k) (m : ℤ) :
    bBminusSeq τ j (m+2*(k:ℤ)) = τ^(2*m+2*(k:ℤ)-1) * bBminusSeq τ j m := by
  apply residueSum_minus_quasiperiod (2*(k:ℤ)) (paperIndex j)
    (fun y => τ^((2*(k:ℤ))*y^2-(2*paperIndex j-1)*y))
    (fun m => τ^(2*m+2*(k:ℤ)-1))
  intro y
  rw [← zpow_add₀ hparam]
  congr 1
  ring

/-- Equation (4.2), affine reflection rewritten in `τ`. -/
theorem gammaBminus_second (τ : F) (hparam : τ ≠ 0) (j : Fin k) (m : ℤ) :
    gammaBminus τ j m = -τ^(2*m-2*(k:ℤ)-1) * gammaBminus τ j (2*(k:ℤ)+1-m) := by
  have ha : τ^(2*(m-2*(k:ℤ))+2*(k:ℤ)-1) * τ^(2*(1-m)+2*(k:ℤ)-1) = 1 := by
    rw [← zpow_add₀ hparam,
      show (2*(m-2*(k:ℤ))+2*(k:ℤ)-1)+(2*(1-m)+2*(k:ℤ)-1) = 0 by ring, zpow_zero]
  have h := center_fold_affine (2*(k:ℤ)) 1 (bBminusSeq τ j)
    (fun m => τ^(2*m+2*(k:ℤ)-1)) (bBminus_quasiperiod τ hparam j) m ha
  have he : 2*(m-2*(k:ℤ))+2*(k:ℤ)-1 = 2*m-2*(k:ℤ)-1 := by ring
  have hi : 1-(2*(k:ℤ)+1-m) = m-2*(k:ℤ) := by ring
  have hs : (-1:F)^(2*(k:ℤ)+1) = -1 := (odd_two_mul_add_one _).neg_one_zpow
  simpa only [gammaBminus, he, hi, hs, neg_one_mul] using h

end BminusSequence

end
end AffineDualJT
