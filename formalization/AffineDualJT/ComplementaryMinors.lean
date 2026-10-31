import AffineDualJT.PaperTopForms
import AffineDualJT.PaperCauchyBinet

/-!
# Complementary minors and the normalized transfer (§3.1)

Theorem 3.1 is proved through the paper's quotient top forms, signed
complementary minors, Cauchy--Binet regrouping, and normalization at the two
reference minors. The complementary shuffle sign is identified with the
paper's explicit `(-1)^(nk) ε(Q)` by counting inversions across the two
increasing blocks.

Proof map for Theorem 3.1: `PaperTopForms` proves both rank/kernel
equalities and quotient isomorphisms, constructs the determinant top forms
using linear sections of the quotient maps, and proves their proportionality
by the abstract top-degree alternating-form lemma. Section-independence,
coordinate-representative evaluation, and the signed complementary-minor
relations for every increasingly ordered finite subset `Q` are now proved.
`PaperCauchyBinet` proves the explicit Leibniz expansion, removes repeated
intermediate indices, groups injective tuples by their increasingly ordered
image subset, and reindexes the `Uᵀ Z` sum by complementary subsets. The main
proof below uses these Cauchy–Binet identities with the quotient-top-form
complementary-minor relations and the explicit subset sign from the paper.
-/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Transfer
variable {F : Type*} [Field F]

/-- Paper p.6, Theorem 3.1. -/
theorem theorem_3_1
    {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (U Z : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0) (hYTZ : Y.transpose * Z = 0)
    (hXQ0 : (firstCols X).det ≠ 0) (hUJ : (tailRowsAfterN U).det ≠ 0)
    (hYH : (lastRowsY Y).det ≠ 0) (hZI : (firstRowsZ Z).det ≠ 0) :
    (X*Y).det =
      ((-1:F)^(n*k)) * ((firstCols X).det * (lastRowsY Y).det) /
        ((tailRowsAfterN U).det * (firstRowsZ Z).det) * (U.transpose*Z).det := by
  classical
  let Qs := {Q : Finset (Fin (n+k)) // Q.card = n}
  let a : F := (-1:F)^(n*k)
  have ha : a*a=1 := by
    dsimp [a]
    rw [← mul_pow]
    simp
  have hminor_sum :
      (∑ Q : Qs,
        (X.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
          (Y.submatrix (Q.1.orderEmbOfFin Q.2) id).det) *
          ((tailRowsAfterN U).det * (firstRowsZ Z).det) =
        a * ((firstCols X).det * (lastRowsY Y).det) *
          ∑ Q : Qs,
            (U.submatrix (Q.1ᶜ.orderEmbOfFin
              (by
                rw [Finset.card_compl, Fintype.card_fin, Q.2]
                omega)) id).det *
              (Z.submatrix (Q.1ᶜ.orderEmbOfFin
                (by
                  rw [Finset.card_compl, Fintype.card_fin, Q.2]
                  omega)) id).det := by
    calc
      _ = ∑ Q : Qs,
          ((X.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
            (Y.submatrix (Q.1.orderEmbOfFin Q.2) id).det) *
            ((tailRowsAfterN U).det * (firstRowsZ Z).det) := by rw [Finset.sum_mul]
      _ = ∑ Q : Qs, a * ((firstCols X).det * (lastRowsY Y).det) *
            ((U.submatrix (Q.1ᶜ.orderEmbOfFin
              (by
                rw [Finset.card_compl, Fintype.card_fin, Q.2]
                omega)) id).det *
              (Z.submatrix (Q.1ᶜ.orderEmbOfFin
                (by
                  rw [Finset.card_compl, Fintype.card_fin, Q.2]
                  omega)) id).det) := by
          apply Finset.sum_congr rfl
          intro Q _
          have hQc : Q.1ᶜ.card = k := by
            rw [Finset.card_compl, Fintype.card_fin, Q.2]
            omega
          let pQ := paperFinsetSplit Q.1 Q.2
          let σ := pQ.trans (paperSplitRows n k).symm
          let εQ : F := (-1:F) ^
            (∑ r : Fin n, ((Q.1.orderEmbOfFin Q.2 r).val-r.val))
          let sQ : F := a * εQ
          have hsignExplicit : ((Equiv.Perm.sign σ : ℤ) : F) = sQ := by
            have hsignUnit := paperFinsetSplit_sign_eq_paperEpsilon Q.1 Q.2
            have hsignInt := congrArg (fun u : ℤˣ => (u : ℤ)) hsignUnit
            have hsignF := congrArg (fun z : ℤ => (z : F)) hsignInt
            simpa [σ, sQ, εQ, a, paperEpsilon, Int.cast_mul] using hsignF
          have hεsq : εQ*εQ=1 := by
            dsimp [εQ]
            rw [← mul_pow]
            simp
          have hsignsq : sQ*sQ=1 := by
            dsimp [sQ]
            calc
              _ = (a*a) * (εQ*εQ) := by ring
              _ = 1 := by rw [ha, hεsq]; ring
          have hX := paper_XU_finset_complement_relation X U hXU hXQ0 hUJ
            Q.1 Q.2
          have hY := paper_YZ_finset_complement_relation Y Z hYTZ hYH hZI
            Q.1 Q.2
          rw [hsignExplicit] at hX hY
          have hX' :
              (X.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
                (a * (tailRowsAfterN U).det) =
              (firstCols X).det *
                (sQ * (U.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det) := by
            exact hX
          have hY' :
              (Y.submatrix (Q.1.orderEmbOfFin Q.2) id).det *
                (firstRowsZ Z).det =
              (lastRowsY Y).det *
                (sQ * (Z.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det) := by
            exact hY
          have hmul := congrArg₂ (· * ·) hX' hY'
          calc
            _ = (a*a) *
                (((X.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
                  (Y.submatrix (Q.1.orderEmbOfFin Q.2) id).det) *
                  ((tailRowsAfterN U).det * (firstRowsZ Z).det)) := by
                    rw [ha]
                    ring
            _ = a *
                (((X.submatrix id (Q.1.orderEmbOfFin Q.2)).det *
                  (a * (tailRowsAfterN U).det)) *
                  ((Y.submatrix (Q.1.orderEmbOfFin Q.2) id).det *
                    (firstRowsZ Z).det)) := by ring
            _ = a *
                ((firstCols X).det *
                  (sQ * (U.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det)) *
                ((lastRowsY Y).det *
                  (sQ * (Z.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det)) := by
                    rw [hX', hY']
                    ring
            _ = a * ((firstCols X).det * (lastRowsY Y).det) *
                (sQ*sQ) *
                ((U.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det *
                  (Z.submatrix (Q.1ᶜ.orderEmbOfFin hQc) id).det) := by ring
            _ = _ := by rw [hsignsq]; ring
      _ = a * ((firstCols X).det * (lastRowsY Y).det) *
            ∑ Q : Qs,
              (U.submatrix (Q.1ᶜ.orderEmbOfFin
                (by
                  rw [Finset.card_compl, Fintype.card_fin, Q.2]
                  omega)) id).det *
                (Z.submatrix (Q.1ᶜ.orderEmbOfFin
                  (by
                    rw [Finset.card_compl, Fintype.card_fin, Q.2]
                    omega)) id).det := by rw [Finset.mul_sum]
  have hcleared :
      (X*Y).det * ((tailRowsAfterN U).det * (firstRowsZ Z).det) =
        a * ((firstCols X).det * (lastRowsY Y).det) * (U.transpose*Z).det := by
    simpa [Qs, a, paper_cauchy_binet, paper_cauchy_binet_complement_sum] using hminor_sum
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hUJ hZI)]
  simpa [a] using hcleared

/-- Denominator-cleared form of Theorem 3.1. -/
theorem theorem_3_1_cleared
    {n k : ℕ}
    (X : Matrix (Fin n) (Fin (n+k)) F)
    (Y : Matrix (Fin (n+k)) (Fin n) F)
    (U Z : Matrix (Fin (n+k)) (Fin k) F)
    (hXU : X * U = 0) (hYTZ : Y.transpose * Z = 0)
    (hXQ0 : (firstCols X).det ≠ 0) (hUJ : (tailRowsAfterN U).det ≠ 0)
    (hYH : (lastRowsY Y).det ≠ 0) (hZI : (firstRowsZ Z).det ≠ 0) :
    (X*Y).det * ((tailRowsAfterN U).det * (firstRowsZ Z).det) =
      ((-1:F)^(n*k)) * ((firstCols X).det * (lastRowsY Y).det) * (U.transpose*Z).det := by
  rw [theorem_3_1 X Y U Z hXU hYTZ hXQ0 hUJ hYH hZI]
  field_simp

/-- Equation (3.1), packaged in the normalization used by the paper. -/
theorem normalized_transfer_3_1
    {n k : ℕ}
    (Phi : Matrix (Fin n) (Fin (n+k)) F)
    (V : Matrix (Fin (n+k)) (Fin n) F)
    (D C : Matrix (Fin (n+k)) (Fin k) F)
    (hPhiD : Phi*D=0) (hVTC : V.transpose*C=0)
    (hDelta : (firstCols Phi).det ≠ 0)
    (hDH : (tailRowsAfterN D).det ≠ 0)
    (hVH : (lastRowsY V).det = 1)
    (hCI : (firstRowsZ C).det ≠ 0) :
    (Phi*V).det / (firstCols Phi).det =
      ((-1:F)^(n*k)) / ((tailRowsAfterN D).det * (firstRowsZ C).det) *
        (D.transpose*C).det := by
  have hYH : (lastRowsY V).det ≠ 0 := by rw [hVH]; exact one_ne_zero
  rw [theorem_3_1 Phi V D C hPhiD hVTC hDelta hDH hYH hCI, hVH]
  field_simp

end Transfer
end
end AffineDualJT
