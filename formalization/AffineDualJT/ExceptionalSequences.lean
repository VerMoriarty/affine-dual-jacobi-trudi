import AffineDualJT.OrdinarySequences

/-!
# Sequences and reflections for the exceptional affine kernels (§5)

Definitions and the reflection lemmas 5.2 and 5.4.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix
open AffineDetSum
noncomputable section

section Ct
variable {F : Type*} [Field F]
variable {k : ℕ}

/-- p.10, §5.1 sequence. -/
def bCt (t : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ q : ℤ, if m = paperIndex j + 2*(k:ℤ)*q then
    (-1:F)^q * t^((k:ℤ)*q^2 + paperIndex j*q) else 0

def cCt (t : F) (j : Fin k) (m : ℤ) : F := bCt t j m - bCt t j (-m)

/-- Integer-shift recurrence used in the affine reflection proof. -/
theorem bCt_quasiperiod (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    bCt t j (m+2*(k:ℤ)) = -t^(m+(k:ℤ)) * bCt t j m := by
  apply residueSum_quasiperiod (2*(k:ℤ)) (paperIndex j)
    (fun q => (-1:F)^q * t^((k:ℤ)*q^2+paperIndex j*q)) (fun m => -t^(m+(k:ℤ)))
  intro q
  rw [zpow_add₀ (by norm_num : (-1:F) ≠ 0)]
  have he : (k:ℤ)*(q+1)^2+paperIndex j*(q+1) =
      (paperIndex j+2*(k:ℤ)*q+(k:ℤ))+((k:ℤ)*q^2+paperIndex j*q) := by ring
  rw [he, zpow_add₀ hparam]
  norm_num
  ring

/-- p.10: affine reflection for the fixed-residue case. -/
theorem cCt_reflection (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    cCt t j m = t^(m-(k:ℤ)) * cCt t j (2*(k:ℤ)-m) := by
  have ha : (-t^((m-2*(k:ℤ))+(k:ℤ))) * (-t^(-m+(k:ℤ))) = 1 := by
    rw [neg_mul_neg, ← zpow_add₀ hparam,
      show (m-2*(k:ℤ)+(k:ℤ))+(-m+(k:ℤ)) = 0 by ring, zpow_zero]
  have h := odd_fold_affine (2*(k:ℤ)) (bCt t j)
    (fun m => -t^(m+(k:ℤ))) (bCt_quasiperiod t hparam j) m ha
  have he : m-2*(k:ℤ)+(k:ℤ) = m-(k:ℤ) := by ring
  have hi : -(2*(k:ℤ)-m) = m-2*(k:ℤ) := by ring
  simpa only [cCt, he, hi, neg_neg] using h

end Ct

section Bplus
variable {F : Type*} [Field F]
variable {k : ℕ}

/-- p.11, equation (5.1). -/
def bBplus (t : F) (j : Fin k) (m : ℤ) : F :=
  ∑ᶠ y : ℤ, if m = paperIndex j - 2*(k:ℤ)*y then
    (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y) else 0

def Gamma (t : F) (j : Fin k) (m : ℤ) : F :=
  (-1:F)^m * (bBplus t j m + bBplus t j (2-m))

/-- Lemma 5.2, first quasi-periodicity. -/
theorem lemma_5_2_quasiperiod (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    bBplus t j (m+2*(k:ℤ)) = - t^(m+(k:ℤ)-1) * bBplus t j m := by
  apply residueSum_minus_quasiperiod (2*(k:ℤ)) (paperIndex j)
    (fun y => (-1:F)^y * t^((k:ℤ)*y^2-(paperIndex j-1)*y))
    (fun m => -t^(m+(k:ℤ)-1))
  intro y
  rw [zpow_sub₀ (by norm_num : (-1:F) ≠ 0)]
  have he : (k:ℤ)*(y-1)^2-(paperIndex j-1)*(y-1) =
      (paperIndex j-2*(k:ℤ)*y+(k:ℤ)-1)+((k:ℤ)*y^2-(paperIndex j-1)*y) := by ring
  rw [he, zpow_add₀ hparam]
  norm_num
  ring
/-- Lemma 5.2, center reflection. -/
theorem lemma_5_2_center (t : F) (j : Fin k) (m : ℤ) :
    Gamma t j (2-m) = Gamma t j m := by
  simp only [Gamma, ← Int.cast_negOnePow F, Int.negOnePow_sub]
  norm_num
  ring
/-- Lemma 5.2, affine reflection (5.2). -/
theorem lemma_5_2_affine (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    Gamma t j m = -t^(m-(k:ℤ)-1) * Gamma t j (2*(k:ℤ)+2-m) := by
  have ha : (-t^((m-2*(k:ℤ))+(k:ℤ)-1)) * (-t^(2-m+(k:ℤ)-1)) = 1 := by
    rw [neg_mul_neg, ← zpow_add₀ hparam,
      show (m-2*(k:ℤ)+(k:ℤ)-1)+(2-m+(k:ℤ)-1) = 0 by ring, zpow_zero]
  have h := center_fold_affine (2*(k:ℤ)) 2 (bBplus t j)
    (fun m => -t^(m+(k:ℤ)-1)) (lemma_5_2_quasiperiod t hparam j) m ha
  have he : m-2*(k:ℤ)+(k:ℤ)-1 = m-(k:ℤ)-1 := by ring
  have hi : 2-(2*(k:ℤ)+2-m) = m-2*(k:ℤ) := by ring
  have hs : (-1:F)^(2*(k:ℤ)+2) = 1 := by
    rw [show 2*(k:ℤ)+2 = 2*((k:ℤ)+1) by ring]
    exact (even_two_mul _).neg_one_zpow
  simpa only [Gamma, he, hi, hs, one_mul] using h

/-- The fixed-index conclusion of Lemma 5.2. -/
theorem lemma_5_2_fixed [CharZero F] (t : F) (hparam : t ≠ 0) (j : Fin k) :
    Gamma t j ((k : ℤ) + 1) = 0 := by
  have h := lemma_5_2_affine t hparam j ((k : ℤ) + 1)
  have h₁ : (k : ℤ) + 1 - k - 1 = 0 := by ring
  have h₂ : 2 * (k : ℤ) + 2 - ((k : ℤ) + 1) = (k : ℤ) + 1 := by ring
  rw [h₁, h₂, zpow_zero, neg_one_mul] at h
  have htwo : (2 : F) * Gamma t j ((k : ℤ) + 1) = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end Bplus

section Bt
variable {F : Type*} [Field F]
variable {k : ℕ}

def aBt (t : F) (j : Fin k) (m : ℤ) : F := bBplus t j m + bBplus t j (m+1)
def cBt (t : F) (j : Fin k) (m : ℤ) : F :=
  (-1:F)^m * (aBt t j m + aBt t j (1-m))
def gammaBt (t : F) (j : Fin k) (m : ℤ) : F := cBt t j m - t*cBt t j (m-1)

/-- Lemma 5.4, equation (5.3). -/
theorem lemma_5_4_eq_5_3 (t : F) (j : Fin k) (m : ℤ) :
    cBt t j m = Gamma t j m - Gamma t j (m+1) := by
  have h₁ : 1 - m + 1 = 2 - m := by ring
  have h₂ : 2 - (m + 1) = 1 - m := by ring
  simp only [cBt, aBt, Gamma, h₁, h₂]
  rw [zpow_add₀ (by norm_num : (-1 : F) ≠ 0)]
  norm_num
  ring
/-- Lemma 5.4, equation (5.4). -/
theorem lemma_5_4_eq_5_4 (t : F) (j : Fin k) (m : ℤ) :
    gammaBt t j m = (1+t)*Gamma t j m - Gamma t j (m+1) - t*Gamma t j (m-1) := by
  simp only [gammaBt, lemma_5_4_eq_5_3, sub_add_cancel]
  ring
/-- Lemma 5.4, equation (5.5). -/
theorem lemma_5_4_eq_5_5 (t : F) (hparam : t ≠ 0) (j : Fin k) (m : ℤ) :
    gammaBt t j m = -t^(m-(k:ℤ)-1) * gammaBt t j (2*(k:ℤ)+2-m) := by
  rw [lemma_5_4_eq_5_4, lemma_5_4_eq_5_4]
  rw [lemma_5_2_affine t hparam j m, lemma_5_2_affine t hparam j (m+1),
    lemma_5_2_affine t hparam j (m-1)]
  have hi₁ : 2*(k:ℤ)+2-(m+1) = (2*(k:ℤ)+2-m)-1 := by ring
  have hi₂ : 2*(k:ℤ)+2-(m-1) = (2*(k:ℤ)+2-m)+1 := by ring
  have hA : t*t^((m-1)-(k:ℤ)-1) = t^(m-(k:ℤ)-1) := by
    rw [show m-(k:ℤ)-1 = 1+((m-1)-(k:ℤ)-1) by ring, zpow_add₀ hparam, zpow_one]
  have hB : t^((m+1)-(k:ℤ)-1) = t*t^(m-(k:ℤ)-1) := by
    rw [show (m+1)-(k:ℤ)-1 = 1+(m-(k:ℤ)-1) by ring, zpow_add₀ hparam, zpow_one]
  rw [hi₁, hi₂, hB]
  calc
    _ = -(1+t)*t^(m-(k:ℤ)-1)*Gamma t j (2*(k:ℤ)+2-m) +
        (t*t^(m-(k:ℤ)-1))*Gamma t j (2*(k:ℤ)+2-m-1) +
        (t*t^((m-1)-(k:ℤ)-1))*Gamma t j (2*(k:ℤ)+2-m+1) := by ring
    _ = _ := by rw [hA]; ring

/-- The fixed-index conclusion of Lemma 5.4. -/
theorem lemma_5_4_fixed [CharZero F] (t : F) (hparam : t ≠ 0) (j : Fin k) :
    gammaBt t j ((k : ℤ) + 1) = 0 := by
  have h := lemma_5_4_eq_5_5 t hparam j ((k : ℤ) + 1)
  have h₁ : (k : ℤ) + 1 - k - 1 = 0 := by ring
  have h₂ : 2 * (k : ℤ) + 2 - ((k : ℤ) + 1) = (k : ℤ) + 1 := by ring
  rw [h₁, h₂, zpow_zero, neg_one_mul] at h
  have htwo : (2 : F) * gammaBt t j ((k : ℤ) + 1) = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end Bt

end
end AffineDualJT
