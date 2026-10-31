import AffineDualJT.HallLittlewoodWeyl
import AffineDualJT.PaperAlternantDivisibility
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The unnumbered type A symmetrizer preceding source.tex (2.2)

The source proof is formalized below: the numerator alternates, is divisible
by the Vandermonde, and has the same total degree, so its quotient is a
scalar. The source's zero-variable recurrence then determines that scalar as
`Vn`. The distinguished variable is `Fin 0`, which is the paper's last
variable after relabeling; alternation gives the same sign to the numerator
and Vandermonde.
-/

namespace AffineDualJT
open scoped BigOperators
open Polynomial
noncomputable section
variable {F : Type*} [Field F]

/- The recurrence for `Vn` stated immediately after the unnumbered symmetrizer identity. -/
theorem Vn_succ (n : ℕ) (t : F) :
    ExternalHL.Vn (n+1) t = (∑ l ∈ Finset.range (n+1), t^l) * ExternalHL.Vn n t := by
  unfold ExternalHL.Vn
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  ring

def pairProduct {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) : M :=
  ∏ a : Fin n, ∏ b : Fin n, if a < b then f a b else 1

/- The denominator in the paper's symmetrizer changes by the sign of a
permutation.  We record this independently of the rational identity: it is
the step that turns the Weyl sum into an alternating polynomial numerator. -/
theorem pairProduct_difference_permutation {n : ℕ} (z : Fin n → F)
    (σ : Equiv.Perm (Fin n)) :
    pairProduct (fun a b => z (σ a) - z (σ b)) =
      (Equiv.Perm.sign σ : F) * pairProduct (fun a b => z a - z b) := by
  classical
  have hp (w : Fin n → F) :
      pairProduct (fun a b => w a - w b) =
        (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, (-1 : F)) *
          (Matrix.vandermonde w).det := by
    have hpair : pairProduct (fun a b => w a - w b) =
        ∏ a : Fin n, ∏ b ∈ Finset.Ioi a, (w a - w b) := by
      unfold pairProduct
      apply Finset.prod_congr rfl
      intro a ha
      rw [← Finset.prod_filter]
      have heq : Finset.univ.filter (fun b : Fin n => a < b) = Finset.Ioi a := by
        ext b
        simp [Finset.mem_Ioi]
      rw [heq]
    rw [hpair, Matrix.det_vandermonde]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a ha
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro b hb
    simp only [Finset.mem_Ioi] at hb
    rw [show w a - w b = (-1 : F) * (w b - w a) by ring]
  rw [hp, hp]
  have hdet : (Matrix.vandermonde (fun i => z (σ i))).det =
      (Equiv.Perm.sign σ : F) * (Matrix.vandermonde z).det := by
    rw [show Matrix.vandermonde (fun i => z (σ i)) =
        (Matrix.vandermonde z).submatrix σ id by
      ext i j
      simp [Matrix.vandermonde]]
    rw [Matrix.det_permute]
  rw [hdet]
  ring

theorem pairProduct_subtype {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin n → Fin n → M) :
    pairProduct f = ∏ a : Fin n, ∏ b : {b : Fin n // a < b}, f a b := by
  classical
  unfold pairProduct
  apply Finset.prod_congr rfl
  intro a _
  rw [← Finset.prod_filter]
  exact Finset.prod_subtype _ (by simp) _

private theorem pairProduct_eq_prod_Ioi {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin n → Fin n → M) :
    pairProduct f = ∏ a : Fin n, ∏ b ∈ Finset.Ioi a, f a b := by
  rw [pairProduct_subtype]
  apply Finset.prod_congr rfl
  intro a ha
  symm
  exact Finset.prod_subtype (Finset.Ioi a) (by intro b; simp [Finset.mem_Ioi]) _

private def skewPairAux {M : Type*} [CommRing M] {n : ℕ}
    (g : Fin n → Fin n → M) (a b : Fin n) : M :=
  if a < b then g a b else if b < a then -g b a else 0

private theorem skewPairAux_anti {M : Type*} [CommRing M] {n : ℕ}
    (g : Fin n → Fin n → M) (a b : Fin n) :
    skewPairAux g a b = -skewPairAux g b a := by
  by_cases hab : a < b
  · simp [skewPairAux, hab, not_lt_of_ge hab.le]
  · by_cases hba : b < a
    · simp [skewPairAux, hab, hba]
    · have : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
      subst b
      simp [skewPairAux]

/-- A product of symmetric factors indexed by unordered pairs is invariant
under relabeling. The proof inserts the permutation sign through an
antisymmetric auxiliary factor, then cancels its square. -/
private theorem pairProduct_comp_eq_of_symmetric {M : Type*} [CommRing M]
    {n : ℕ} (g : Fin n → Fin n → M) (hgs : ∀ a b, g a b = g b a)
    (σ : Equiv.Perm (Fin n)) :
    pairProduct (fun a b => g (σ a) (σ b)) = pairProduct g := by
  classical
  let f := skewPairAux g
  have hf (a b : Fin n) : f a b = -f b a := skewPairAux_anti g a b
  have hfac (a b : Fin n) (hab : a < b) :
      f (σ a) (σ b) = (if σ a < σ b then 1 else -1) * g (σ a) (σ b) := by
    have hne : σ a ≠ σ b := fun h => hab.ne (σ.injective h)
    by_cases h : σ a < σ b
    · simp [f, skewPairAux, h]
    · have h' : σ b < σ a := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      simp [f, skewPairAux, h, h', hgs]
  have hfactor : pairProduct (fun a b => f (σ a) (σ b)) =
      ((Equiv.Perm.sign σ : ℤ) : M) *
        pairProduct (fun a b => g (σ a) (σ b)) := by
    rw [pairProduct_eq_prod_Ioi, pairProduct_eq_prod_Ioi]
    calc
      (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, f (σ a) (σ b)) =
          ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
            ((if σ a < σ b then (1 : M) else -1) * g (σ a) (σ b)) := by
              apply Finset.prod_congr rfl
              intro a ha
              apply Finset.prod_congr rfl
              intro b hb
              exact hfac a b (Finset.mem_Ioi.mp hb)
      _ = (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, (if σ a < σ b then (1 : M) else -1)) *
            (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, g (σ a) (σ b)) := by
              simp_rw [Finset.prod_mul_distrib]
      _ = ((Equiv.Perm.sign σ : ℤ) : M) *
            (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, g (σ a) (σ b)) := by
              have hsInt : (σ.sign : ℤ) =
                  ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
                    (if σ a < σ b then (1 : ℤ) else -1) := by
                have hval := congrArg Units.val (Equiv.Perm.sign_eq_prod_prod_Ioi σ)
                let u (a b : Fin n) : ℤˣ := if σ a < σ b then 1 else -1
                calc
                  (σ.sign : ℤ) = (∏ a : Fin n, ∏ b ∈ Finset.Ioi a, u a b : ℤ) := by
                    simpa [u] using hval
                  _ = ∏ a : Fin n, ∏ b ∈ Finset.Ioi a, (u a b : ℤ) := by rfl
                  _ = _ := by
                    apply Finset.prod_congr rfl
                    intro a ha
                    apply Finset.prod_congr rfl
                    intro b hb
                    by_cases h : σ a < σ b <;> simp [u, h]
              have hsM : ((Equiv.Perm.sign σ : ℤ) : M) =
                  ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
                    (if σ a < σ b then (1 : M) else -1) := by
                have hcastIte (a b : Fin n) :
                    (Int.castRingHom M) (if σ a < σ b then (1 : ℤ) else -1) =
                      (if σ a < σ b then (1 : M) else -1) := by
                  by_cases h : σ a < σ b <;> simp [h]
                calc
                  ((Equiv.Perm.sign σ : ℤ) : M) =
                      (Int.castRingHom M)
                        (∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
                          (if σ a < σ b then (1 : ℤ) else -1)) := by
                            rw [hsInt]
                            rfl
                  _ = ∏ a : Fin n, ∏ b ∈ Finset.Ioi a,
                        (if σ a < σ b then (1 : M) else -1) := by
                          rw [map_prod]
                          apply Finset.prod_congr rfl
                          intro a ha
                          rw [map_prod]
                          apply Finset.prod_congr rfl
                          intro b hb
                          exact hcastIte a b
              rw [← hsM]
  have hskew : pairProduct (fun a b => f (σ a) (σ b)) =
      ((Equiv.Perm.sign σ : ℤ) : M) * pairProduct f := by
    rw [pairProduct_eq_prod_Ioi, pairProduct_eq_prod_Ioi]
    exact Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod σ hf
  have hbase : pairProduct f = pairProduct g := by
    rw [pairProduct_eq_prod_Ioi, pairProduct_eq_prod_Ioi]
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    simp [f, skewPairAux, Finset.mem_Ioi.mp hb]
  have hsquare : (((Equiv.Perm.sign σ : ℤ) : M))^2 = 1 := by
    have h : Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by
      rw [← Equiv.Perm.sign_mul]
      simp
    have hz := congrArg Units.val h
    simp only [Units.val_mul, Units.val_one] at hz
    have hf := congrArg (Int.castRingHom M) hz
    rw [map_mul, map_one] at hf
    simpa [pow_two] using hf
  have heq := hskew.symm.trans hfactor
  rw [hbase] at heq
  change ((Equiv.Perm.sign σ : ℤ) : M) * pairProduct g =
    ((Equiv.Perm.sign σ : ℤ) : M) * pairProduct (fun a b => g (σ a) (σ b)) at heq
  calc
    pairProduct (fun a b => g (σ a) (σ b)) =
        1 * pairProduct (fun a b => g (σ a) (σ b)) := by simp
    _ = (((Equiv.Perm.sign σ : ℤ) : M) * ((Equiv.Perm.sign σ : ℤ) : M)) *
        pairProduct (fun a b => g (σ a) (σ b)) := by rw [one_mul, ← pow_two, hsquare]; simp
    _ = ((Equiv.Perm.sign σ : ℤ) : M) *
        (((Equiv.Perm.sign σ : ℤ) : M) *
          pairProduct (fun a b => g (σ a) (σ b))) := by ring
    _ = ((Equiv.Perm.sign σ : ℤ) : M) *
        (((Equiv.Perm.sign σ : ℤ) : M) * pairProduct g) := by rw [heq.symm]
    _ = ((Equiv.Perm.sign σ : ℤ) : M)^2 * pairProduct g := by ring
    _ = pairProduct g := by rw [hsquare]; simp

/-- The ordered pair indices in the alternating numerator of the paper's
unnumbered symmetrizer identity. -/
abbrev SymmetrizerPairIndex (n : ℕ) := Σ a : Fin n, {b : Fin n // a < b}

/-- The paper's alternating numerator `A_n(t,z)`, represented as a polynomial
in the node variables. The parameter `t` is specialized in the coefficient
field, while the node variables remain indeterminates. -/
def symmetrizerAlternantPolynomial {n : ℕ} (t : F) : MvPolynomial (Fin n) F :=
  ∑ σ : Equiv.Perm (Fin n),
    MvPolynomial.C (Equiv.Perm.sign σ : F) *
      pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
        MvPolynomial.X (σ b))

private def symmetrizerInverseFactor {n : ℕ} (t : F) (τ : Equiv.Perm (Fin n))
    (i j : Fin n) : MvPolynomial (Fin n) F :=
  if τ i < τ j then MvPolynomial.C t * MvPolynomial.X i - MvPolynomial.X j
  else MvPolynomial.C t * MvPolynomial.X j - MvPolynomial.X i

private theorem symmetrizerInverseFactor_symmetric {n : ℕ} (t : F)
    (τ : Equiv.Perm (Fin n)) (i j : Fin n) :
    symmetrizerInverseFactor t τ i j = symmetrizerInverseFactor t τ j i := by
  by_cases h : τ i < τ j
  · simp [symmetrizerInverseFactor, h, not_lt_of_ge h.le]
  · by_cases h' : τ j < τ i
    · simp [symmetrizerInverseFactor, h, h']
    · have hij : τ i = τ j := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      have hij' : i = j := τ.injective hij
      subst j
      simp [symmetrizerInverseFactor]

private def symmetrizerInverseTerm {n : ℕ} (t : F) (τ : Equiv.Perm (Fin n)) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C (Equiv.Perm.sign τ : F) *
    pairProduct (symmetrizerInverseFactor t τ)

/-- The alternant indexed by inverse permutations. This form exposes the
position of a distinguished variable and is used for the source's zero-node
recurrence. -/
private def symmetrizerInverseAlternantPolynomial {n : ℕ} (t : F) :
    MvPolynomial (Fin n) F :=
  ∑ τ : Equiv.Perm (Fin n), symmetrizerInverseTerm t τ

private theorem symmetrizerAlternantTerm_eq_inverseTerm {n : ℕ} (t : F)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.C (Equiv.Perm.sign σ : F) *
        pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
          MvPolynomial.X (σ b)) =
      symmetrizerInverseTerm t σ.symm := by
  have hsym (i j : Fin n) := symmetrizerInverseFactor_symmetric t σ.symm i j
  have hfactor (a b : Fin n) (hab : a < b) :
      symmetrizerInverseFactor t σ.symm (σ a) (σ b) =
        MvPolynomial.C t * MvPolynomial.X (σ a) - MvPolynomial.X (σ b) := by
    simp [symmetrizerInverseFactor, hab]
  have hpair :
      pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
        MvPolynomial.X (σ b)) =
        pairProduct (symmetrizerInverseFactor t σ.symm) := by
    calc
      pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
          MvPolynomial.X (σ b)) =
          pairProduct (fun a b => symmetrizerInverseFactor t σ.symm (σ a) (σ b)) := by
            rw [pairProduct_subtype, pairProduct_subtype]
            apply Finset.prod_congr rfl
            intro a ha
            apply Finset.prod_congr rfl
            intro b hb
            exact (hfactor a b b.property).symm
      _ = pairProduct (symmetrizerInverseFactor t σ.symm) :=
          pairProduct_comp_eq_of_symmetric
            (symmetrizerInverseFactor t σ.symm) hsym σ
  have hsign : ((Equiv.Perm.sign σ : ℤ) : F) =
      ((Equiv.Perm.sign σ.symm : ℤ) : F) := by
    simp
  simp only [symmetrizerInverseTerm, hsign, hpair]

theorem symmetrizerAlternantPolynomial_eq_inverse {n : ℕ} (t : F) :
    symmetrizerAlternantPolynomial (n := n) t =
      symmetrizerInverseAlternantPolynomial (n := n) t := by
  classical
  unfold symmetrizerAlternantPolynomial symmetrizerInverseAlternantPolynomial
  calc
    (∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.C (Equiv.Perm.sign σ : F) *
          pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
            MvPolynomial.X (σ b))) =
        ∑ σ : Equiv.Perm (Fin n), symmetrizerInverseTerm t σ.symm := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact symmetrizerAlternantTerm_eq_inverseTerm t σ
    _ = ∑ τ : Equiv.Perm (Fin n), symmetrizerInverseTerm t τ := by
          exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
            (symmetrizerInverseTerm t)

private theorem symmetrizer_zero_position_coefficient {N : ℕ} (p : ℕ)
    (hp : p ≤ N) (t : F) :
    (∏ q : Fin N, if p ≤ q.val then (-1 : F) else t) =
      t^p * (-1)^(N-p) := by
  classical
  have hfin : (∏ q : Fin N, if p ≤ q.val then (-1 : F) else t) =
      ∏ i ∈ Finset.range N, if p ≤ i then (-1 : F) else t := by
    simpa using (Fin.prod_univ_eq_prod_range
      (fun i : ℕ => if p ≤ i then (-1 : F) else t) N)
  rw [hfin]
  have hge : (Finset.range N).filter (fun i => p ≤ i) = Finset.Ico p N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hlt : (Finset.range N).filter (fun i => ¬ p ≤ i) = Finset.range p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.prod_ite, hge, hlt]
  simp [Finset.prod_const, Nat.card_Ico, Finset.card_range, mul_comm]

private theorem symmetrizer_zero_position_factor_product {n : ℕ}
    (t : F) (z : Fin (n+1) → F) (p : Fin (n+2))
    (ρ : Equiv.Perm (Fin (n+1))) :
    (∏ j : Fin (n+1),
      if p.val ≤ (ρ j).val then -z j else t * z j) =
      t^p.val * (-1)^((n+1)-p.val) * ∏ j : Fin (n+1), z j := by
  have hp : p.val ≤ n+1 := Nat.le_of_lt_succ p.isLt
  calc
    (∏ j : Fin (n+1),
        if p.val ≤ (ρ j).val then -z j else t * z j) =
        (∏ j : Fin (n+1), if p.val ≤ (ρ j).val then (-1 : F) else t) *
          ∏ j : Fin (n+1), z j := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro j hj
            by_cases h : p.val ≤ (ρ j).val <;> simp [h]
    _ = (∏ j : Fin (n+1), if p.val ≤ j.val then (-1 : F) else t) *
          ∏ j : Fin (n+1), z j := by
            congr 1
            exact Equiv.prod_comp ρ (fun j : Fin (n+1) =>
              if p.val ≤ j.val then (-1 : F) else t)
    _ = t^p.val * (-1)^((n+1)-p.val) * ∏ j : Fin (n+1), z j := by
          rw [symmetrizer_zero_position_coefficient (p := p.val) hp t]

private theorem eval_pairProduct_F02 {n : ℕ} (z : Fin n → F)
    (f : Fin n → Fin n → MvPolynomial (Fin n) F) :
    MvPolynomial.eval z (pairProduct f) =
      pairProduct (fun a b => MvPolynomial.eval z (f a b)) := by
  unfold pairProduct
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro b hb
  by_cases h : a < b <;> simp [h]

private theorem pairProduct_succ_F02 {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n+1) → Fin (n+1) → M) :
    pairProduct f = (∏ b : Fin n, f 0 b.succ) *
      pairProduct (fun a b : Fin n => f a.succ b.succ) := by
  classical
  unfold pairProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, lt_self_iff_false, ite_false, one_mul,
    Fin.succ_pos, ite_true, Fin.not_lt_zero, Fin.succ_lt_succ_iff]

private theorem eval_symmetrizerInverseTerm_decomposeFin'Symm {n : ℕ}
    (t : F) (z : Fin (n+1) → F) (p : Fin (n+2))
    (ρ : Equiv.Perm (Fin (n+1))) :
    MvPolynomial.eval (Fin.cons (0 : F) z)
        (symmetrizerInverseTerm t (Equiv.Perm.decomposeFin'Symm p ρ)) =
      ((-1 : F)^(n+1)) * t^p.val * (∏ j : Fin (n+1), z j) *
        MvPolynomial.eval z (symmetrizerInverseTerm t ρ) := by
  let τ := Equiv.Perm.decomposeFin'Symm p ρ
  have hedge (j : Fin (n+1)) :
      MvPolynomial.eval (Fin.cons (0 : F) z)
          (symmetrizerInverseFactor t τ 0 j.succ) =
        if p.val ≤ (ρ j).val then -z j else t * z j := by
    simp only [symmetrizerInverseFactor, τ,
      Equiv.Perm.decomposeFin'Symm_zero, Equiv.Perm.decomposeFin'Symm_succ]
    have hcond : p < p.succAbove (ρ j) ↔ p.val ≤ (ρ j).val := by
      rw [Fin.lt_succAbove_iff_le_castSucc, Fin.le_iff_val_le_val]
      simp
    by_cases h : p < p.succAbove (ρ j)
    · have hh := hcond.mp h
      simp [h, hh, MvPolynomial.eval_C, MvPolynomial.eval_X]
    · have hh : ¬ p.val ≤ (ρ j).val := fun hh => h (hcond.mpr hh)
      simp [h, hh, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have htail (a b : Fin (n+1)) :
      MvPolynomial.eval (Fin.cons (0 : F) z)
          (symmetrizerInverseFactor t τ a.succ b.succ) =
        MvPolynomial.eval z (symmetrizerInverseFactor t ρ a b) := by
    simp only [symmetrizerInverseFactor, τ,
      Equiv.Perm.decomposeFin'Symm_succ]
    by_cases h : ρ a < ρ b <;>
      simp [h, Fin.succAbove_lt_succAbove_iff, Fin.cons_succ,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
  have htailProd :
      pairProduct (fun a b : Fin (n+1) =>
        MvPolynomial.eval (Fin.cons (0 : F) z)
          (symmetrizerInverseFactor t τ a.succ b.succ)) =
      pairProduct (fun a b : Fin (n+1) =>
        MvPolynomial.eval z (symmetrizerInverseFactor t ρ a b)) := by
    unfold pairProduct
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    by_cases hab : a < b
    · simp [hab, htail a b]
    · simp [hab]
  have hpair :
      MvPolynomial.eval (Fin.cons (0 : F) z)
          (pairProduct (symmetrizerInverseFactor t τ)) =
        (∏ j : Fin (n+1),
          MvPolynomial.eval (Fin.cons (0 : F) z)
            (symmetrizerInverseFactor t τ 0 j.succ)) *
          pairProduct (fun a b : Fin (n+1) =>
            MvPolynomial.eval z (symmetrizerInverseFactor t ρ a b)) := by
    rw [eval_pairProduct_F02, pairProduct_succ_F02]
    rw [htailProd]
  have hsign : ((Equiv.Perm.sign τ : ℤ) : F) =
      (-1 : F)^p.val * ((Equiv.Perm.sign ρ : ℤ) : F) := by
    have h := congrArg (fun u : ℤˣ => ((u : ℤ) : F))
      (Equiv.Perm.sign_decomposeFin'Symm p ρ)
    simp [τ]
  rw [symmetrizerInverseTerm, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    hpair]
  rw [Finset.prod_congr rfl (fun j _ => hedge j)]
  rw [symmetrizer_zero_position_factor_product]
  rw [show MvPolynomial.eval z (symmetrizerInverseTerm t ρ) =
      ((Equiv.Perm.sign ρ : ℤ) : F) *
        pairProduct (fun a b => MvPolynomial.eval z
          (symmetrizerInverseFactor t ρ a b)) by
        simp [symmetrizerInverseTerm, eval_pairProduct_F02]]
  rw [hsign]
  have hp : p.val + ((n+1)-p.val) = n+1 := Nat.add_sub_of_le
    (Nat.le_of_lt_succ p.isLt)
  have hpw : (-1 : F)^p.val * (-1)^((n+1)-p.val) = (-1 : F)^(n+1) := by
    rw [← pow_add, hp]
  calc
    (-1 : F)^p.val * ((Equiv.Perm.sign ρ : ℤ) : F) *
        (t^p.val * (-1)^((n+1)-p.val) * (∏ j, z j) *
          pairProduct (fun a b => MvPolynomial.eval z
            (symmetrizerInverseFactor t ρ a b))) =
      ((-1 : F)^p.val * (-1)^((n+1)-p.val)) * t^p.val *
        (∏ j, z j) * ((Equiv.Perm.sign ρ : ℤ) : F) *
          pairProduct (fun a b => MvPolynomial.eval z
            (symmetrizerInverseFactor t ρ a b)) := by ac_rfl
    _ = (-1 : F)^(n+1) * t^p.val * (∏ j, z j) *
        ((Equiv.Perm.sign ρ : ℤ) : F) *
          pairProduct (fun a b => MvPolynomial.eval z
            (symmetrizerInverseFactor t ρ a b)) := by
              rw [hpw]
    _ = (-1 : F)^(n+1) * t^p.val * (∏ j, z j) *
        (((Equiv.Perm.sign ρ : ℤ) : F) *
          pairProduct (fun a b => MvPolynomial.eval z
            (symmetrizerInverseFactor t ρ a b))) := by
              exact mul_assoc _ _ _

/-- Source's zero-variable-position recurrence. After reindexing by the
inverse permutation, `p` is the position of the distinguished zero variable.
The zero-variable pair factors contribute `t^p` times the product of the
remaining variables; the permutation sign cancels their `(-1)` factors. -/
theorem symmetrizerAlternantPolynomial_zeroHead {n : ℕ} (t : F)
    (z : Fin (n+1) → F) :
    MvPolynomial.eval (Fin.cons (0 : F) z)
        (symmetrizerAlternantPolynomial (n := n+2) t) =
      ((-1 : F)^(n+1)) *
        (∑ p ∈ Finset.range (n+2), t^p) *
        (∏ j : Fin (n+1), z j) *
        MvPolynomial.eval z (symmetrizerAlternantPolynomial (n := n+1) t) := by
  classical
  rw [symmetrizerAlternantPolynomial_eq_inverse]
  unfold symmetrizerInverseAlternantPolynomial
  rw [← (Equiv.Perm.decomposeFin' (n := n)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin'_symm]
  simp only [map_sum]
  calc
    (∑ p : Fin (n+2), ∑ ρ : Equiv.Perm (Fin (n+1)),
        MvPolynomial.eval (Fin.cons (0 : F) z)
          (symmetrizerInverseTerm t (Equiv.Perm.decomposeFin'Symm p ρ))) =
      ∑ p : Fin (n+2), ∑ ρ : Equiv.Perm (Fin (n+1)),
        ((-1 : F)^(n+1)) * t^p.val * (∏ j : Fin (n+1), z j) *
          MvPolynomial.eval z (symmetrizerInverseTerm t ρ) := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro ρ hρ
            exact eval_symmetrizerInverseTerm_decomposeFin'Symm t z p ρ
    _ = ((-1 : F)^(n+1)) *
          (∑ p ∈ Finset.range (n+2), t^p) *
          (∏ j : Fin (n+1), z j) *
          MvPolynomial.eval z (symmetrizerAlternantPolynomial (n := n+1) t) := by
            have hsumρ :
                (∑ ρ : Equiv.Perm (Fin (n+1)),
                  MvPolynomial.eval z (symmetrizerInverseTerm t ρ)) =
                  MvPolynomial.eval z
                    (symmetrizerAlternantPolynomial (n := n+1) t) := by
              calc
                _ = MvPolynomial.eval z
                    (∑ ρ : Equiv.Perm (Fin (n+1)),
                      symmetrizerInverseTerm t ρ) := by
                        symm
                        exact map_sum (MvPolynomial.eval z)
                          (fun ρ : Equiv.Perm (Fin (n+1)) =>
                            symmetrizerInverseTerm t ρ) Finset.univ
                _ = MvPolynomial.eval z
                    (symmetrizerAlternantPolynomial (n := n+1) t) := by
                        rw [symmetrizerAlternantPolynomial_eq_inverse]
                        rfl
            have hinner (p : Fin (n+2)) :
                (∑ ρ : Equiv.Perm (Fin (n+1)),
                  ((-1 : F)^(n+1)) * t^p.val *
                    (∏ j : Fin (n+1), z j) *
                    MvPolynomial.eval z (symmetrizerInverseTerm t ρ)) =
                  ((-1 : F)^(n+1)) * t^p.val *
                    (∏ j : Fin (n+1), z j) *
                    (∑ ρ : Equiv.Perm (Fin (n+1)),
                      MvPolynomial.eval z (symmetrizerInverseTerm t ρ)) := by
              rw [← Finset.mul_sum]
            rw [Finset.sum_congr rfl (fun p _ => hinner p)]
            rw [hsumρ]
            calc
              _ = ∑ p : Fin (n+2),
                    (((-1 : F)^(n+1)) * (∏ j : Fin (n+1), z j) *
                      MvPolynomial.eval z
                        (symmetrizerAlternantPolynomial (n := n+1) t)) * t^p.val := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      ac_rfl
              _ = (((-1 : F)^(n+1)) * (∏ j : Fin (n+1), z j) *
                      MvPolynomial.eval z
                        (symmetrizerAlternantPolynomial (n := n+1) t)) *
                    (∑ p : Fin (n+2), t^p.val) := by
                      rw [← Finset.mul_sum]
              _ = ((-1 : F)^(n+1)) *
                    (∑ p ∈ Finset.range (n+2), t^p) *
                    (∏ j : Fin (n+1), z j) *
                    MvPolynomial.eval z (symmetrizerAlternantPolynomial (n := n+1) t) := by
                      rw [Fin.sum_univ_eq_sum_range]
                      ac_rfl

/-- The Vandermonde `Δ_n=∏_{a<b}(z_a-z_b)` with the orientation used in
the paper's symmetrizer proof. -/
def symmetrizerVandermondePolynomial {n : ℕ} : MvPolynomial (Fin n) F :=
  pairProduct (fun a b => MvPolynomial.X a - MvPolynomial.X b)

private theorem eval_pairProduct {n : ℕ} (z : Fin n → F)
    (f : Fin n → Fin n → MvPolynomial (Fin n) F) :
    MvPolynomial.eval z (pairProduct f) =
      pairProduct (fun a b => MvPolynomial.eval z (f a b)) := by
  unfold pairProduct
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro b hb
  by_cases h : a < b <;> simp [h]

theorem eval_symmetrizerAlternantPolynomial {n : ℕ} (t : F) (z : Fin n → F) :
    MvPolynomial.eval z (symmetrizerAlternantPolynomial t) =
      ∑ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : F) *
          pairProduct (fun a b => t * z (σ a) - z (σ b)) := by
  simp [symmetrizerAlternantPolynomial, eval_pairProduct, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_mul, map_sub]

set_option maxHeartbeats 1000000 in
/-- The polynomial numerator in the paper is alternating in the variables.
This records the exact permutation action before using divisibility by the
Vandermonde. -/
theorem symmetrizerAlternantPolynomial_rename {n : ℕ} (t : F)
    (e : Equiv.Perm (Fin n)) :
    MvPolynomial.rename e (symmetrizerAlternantPolynomial t) =
      MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : F) *
        symmetrizerAlternantPolynomial t := by
  classical
  unfold symmetrizerAlternantPolynomial
  have hprod (σ : Equiv.Perm (Fin n)) :
      MvPolynomial.rename e
          (pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
            MvPolynomial.X (σ b))) =
        pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X ((e * σ) a) -
          MvPolynomial.X ((e * σ) b)) := by
    unfold pairProduct
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro a ha
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro b hb
    by_cases hab : a < b
    · simp [hab, MvPolynomial.rename_X]
    · simp [hab]
  let g (τ : Equiv.Perm (Fin n)) : MvPolynomial (Fin n) F :=
    MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : F) *
      pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (τ a) -
        MvPolynomial.X (τ b))
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : F) *
          pairProduct (fun a b => MvPolynomial.C t *
            MvPolynomial.X ((e * σ) a) - MvPolynomial.X ((e * σ) b)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [map_mul, MvPolynomial.rename_C, hprod]
    _ = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : F) *
        (∑ σ : Equiv.Perm (Fin n), g (e * σ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro σ hσ
          dsimp [g]
          have hcomp : e⁻¹ * (e * σ) = σ := by group
          have hs : ((Equiv.Perm.sign σ : ℤ) : F) =
              ((Equiv.Perm.sign e : ℤ) : F) *
                ((Equiv.Perm.sign (e * σ) : ℤ) : F) := by
            rw [← hcomp, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
            simp
          rw [hs]
          have hpair :
              pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X ((e * σ) a) -
                MvPolynomial.X ((e * σ) b)) =
              pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (e (σ a)) -
                MvPolynomial.X (e (σ b))) := by
            rfl
          calc
            MvPolynomial.C
                  (((Equiv.Perm.sign e : ℤ) : F) *
                    ((Equiv.Perm.sign (e * σ) : ℤ) : F)) *
                pairProduct (fun a b => MvPolynomial.C t *
                  MvPolynomial.X ((e * σ) a) - MvPolynomial.X ((e * σ) b)) =
              (MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : F) *
                MvPolynomial.C ((Equiv.Perm.sign (e * σ) : ℤ) : F)) * _ := by
                  rw [← MvPolynomial.C_mul]
            _ = _ := by rw [hpair]; ring
    _ = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : F) *
        (∑ τ : Equiv.Perm (Fin n), g τ) := by
          congr 1
          simpa only [Equiv.coe_mulLeft] using
            (Equiv.sum_comp (Equiv.mulLeft e) g)
    _ = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : F) *
          symmetrizerAlternantPolynomial t := by rfl

set_option maxHeartbeats 1000000
/-- The alternant numerator vanishes when two node variables are identified.
This is the root step in the paper's Vandermonde-divisibility argument. -/
theorem symmetrizerAlternant_last_difference_dvd [CharZero F] {n : ℕ} (t : F)
    (j : Fin n) :
    (MvPolynomial.X 0 - MvPolynomial.X j.succ : MvPolynomial (Fin n.succ) F) ∣
      symmetrizerAlternantPolynomial t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let f : F →+* K := φ.comp MvPolynomial.C
  let c : R := MvPolynomial.X j
  let root : K := φ c
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hzEq : z j.succ = z 0 := by simp [z, root, c]
  let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 j.succ
  have hze : z ∘ e = z := by
    funext i
    by_cases h0 : i = 0
    · subst i
      simp [e, z, root, c]
    · by_cases hj : i = j.succ
      · subst i
        simp [e, z, root, c]
      · change z (Equiv.swap 0 j.succ i) = z i
        rw [Equiv.swap_apply_of_ne_of_ne h0 hj]
  have hsign : ((Equiv.Perm.sign e : ℤ) : F) = -1 := by
    dsimp [e]
    rw [Equiv.Perm.sign_swap (Fin.succ_ne_zero j).symm]
    norm_num
  have hrename : MvPolynomial.rename e (symmetrizerAlternantPolynomial t) =
      -symmetrizerAlternantPolynomial t := by
    simpa [hsign] using symmetrizerAlternantPolynomial_rename t e
  have heval : MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) = 0 := by
    have hleft : MvPolynomial.eval₂Hom f z
        (MvPolynomial.rename e (symmetrizerAlternantPolynomial t)) =
        MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) := by
      rw [MvPolynomial.eval₂Hom_rename, hze]
    have hright : MvPolynomial.eval₂Hom f z
        (MvPolynomial.rename e (symmetrizerAlternantPolynomial t)) =
        -MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) := by
      rw [hrename]
      simp
    have hneg : MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) =
        -MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) :=
      hleft.symm.trans hright
    have hmul : (2 : K) *
        MvPolynomial.eval₂Hom f z (symmetrizerAlternantPolynomial t) = 0 := by
      linear_combination hneg
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  let E := MvPolynomial.finSuccEquiv F n
  let p : Polynomial R := E (symmetrizerAlternantPolynomial t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : ψ.comp E.toRingHom = MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [ψ, f, E, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, E, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, E, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (symmetrizerAlternantPolynomial t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hprimitive : (Polynomial.X - Polynomial.C c).IsPrimitive :=
    (Polynomial.monic_X_sub_C c).isPrimitive
  have hmap_dvd : (Polynomial.X - Polynomial.C c).map φ ∣ p.map φ := by
    have hm : (Polynomial.X - Polynomial.C c).map φ =
        Polynomial.X - Polynomial.C root := by simp [root, c]
    simpa [hm] using hroot_dvd
  have hpoly_dvd : (Polynomial.X - Polynomial.C c) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨E.symm q, ?_⟩
  have hc : E (MvPolynomial.X (R := F) (σ := Fin n.succ) j.succ) =
      Polynomial.C (MvPolynomial.X (R := F) (σ := Fin n) j) := by
    simp [E, MvPolynomial.finSuccEquiv_X_succ]
  have hfactor : E (MvPolynomial.X (R := F) (σ := Fin n.succ) 0 -
      MvPolynomial.X (R := F) (σ := Fin n.succ) j.succ) =
      Polynomial.X - Polynomial.C c := by
    simp [E, hc, c, MvPolynomial.finSuccEquiv_X_zero]
  apply E.injective
  change E (symmetrizerAlternantPolynomial t) =
    E ((MvPolynomial.X (R := F) (σ := Fin n.succ) 0 -
      MvPolynomial.X (R := F) (σ := Fin n.succ) j.succ) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (Polynomial.X - Polynomial.C c) * q
  exact hq

set_option maxHeartbeats 1000000
/-- Transport the first-variable root factor to any ordered pair by the
alternation law. -/
theorem symmetrizerAlternant_difference_dvd [CharZero F] {n : ℕ} (t : F)
    (a b : Fin n) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F) ∣
      symmetrizerAlternantPolynomial t := by
  classical
  cases n with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro hzero
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [hzero]
          _ = b := he0
      exact hab this
    have hpos : 0 < (e.symm a).val := by
      by_contra! hnonpos
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero hnonpos
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have hh := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by rw [hjs, e.apply_symm_apply]
    have hbase := symmetrizerAlternant_last_difference_dvd (F := F) t j
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
        MvPolynomial.X b - MvPolynomial.X a := by
      change MvPolynomial.rename e (MvPolynomial.X 0 - MvPolynomial.X j.succ) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant : ρ (symmetrizerAlternantPolynomial t) =
        MvPolynomial.C s * symmetrizerAlternantPolynomial t := by
      change MvPolynomial.rename e (symmetrizerAlternantPolynomial t) = _
      simpa [s] using symmetrizerAlternantPolynomial_rename t e
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hsign | hsign <;>
        simp [hsign]
    have hCs : MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨-(MvPolynomial.C (s⁻¹) * q), ?_⟩
    calc
      symmetrizerAlternantPolynomial t = MvPolynomial.C (s⁻¹) *
          (MvPolynomial.C s * symmetrizerAlternantPolynomial t) := by
            rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) * ((MvPolynomial.X b - MvPolynomial.X a) * q) := by
            rw [← hq]
      _ = (MvPolynomial.X a - MvPolynomial.X b) *
          (-(MvPolynomial.C (s⁻¹) * q)) := by ring

def symmetrizerVandermondePairProduct {n : ℕ} : MvPolynomial (Fin n) F :=
  ∏ p : SymmetrizerPairIndex n,
    (MvPolynomial.X p.1 - MvPolynomial.X p.2.1)

theorem symmetrizerVandermondePairProduct_eq {n : ℕ} :
    symmetrizerVandermondePairProduct (F := F) (n := n) =
      symmetrizerVandermondePolynomial (F := F) (n := n) := by
  classical
  unfold symmetrizerVandermondePairProduct SymmetrizerPairIndex
  rw [Fintype.prod_sigma, symmetrizerVandermondePolynomial, pairProduct_subtype]

set_option maxHeartbeats 1000000
/-- Every factor of the Vandermonde divides the alternating numerator. -/
theorem symmetrizerAlternant_vandermonde_dvd [CharZero F] {n : ℕ} (t : F) :
    symmetrizerVandermondePolynomial (F := F) (n := n) ∣
      symmetrizerAlternantPolynomial (n := n) t := by
  classical
  rw [← symmetrizerVandermondePairProduct_eq (F := F) (n := n)]
  apply Fintype.prod_dvd_of_isRelPrime
  · intro p q hpq
    have hcoords : p.1 ≠ q.1 ∨ p.2.1 ≠ q.2.1 := by
      by_contra hn
      push Not at hn
      apply hpq
      cases p with
      | mk a pa =>
        cases q with
        | mk b pb =>
          simp only [Sigma.mk.inj_iff] at hn ⊢
          rcases hn with ⟨hab, hcd⟩
          cases hab
          exact ⟨rfl, heq_of_eq (Subtype.ext hcd)⟩
    exact paper_difference_isRelPrime_difference
      p.1 p.2.1 q.1 q.2.1 p.2.2 q.2.2 hcoords
  · intro p
    exact symmetrizerAlternant_difference_dvd t p.1 p.2.1 p.2.2.ne

private theorem totalDegree_finsetProd_eq_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial σ F)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      MvPolynomial.totalDegree_mul_of_isDomain (hf a (Finset.mem_insert_self ..))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem symmetrizerPairProduct_degree_le {n : ℕ}
    (g : Fin n → Fin n → MvPolynomial (Fin n) F)
    (hg : ∀ a b, a < b → (g a b).totalDegree ≤ 1) :
    (pairProduct g).totalDegree ≤ Fintype.card (SymmetrizerPairIndex n) := by
  classical
  rw [pairProduct_subtype]
  calc
    (∏ a : Fin n, ∏ b : {b : Fin n // a < b}, g a b).totalDegree
        ≤ ∑ a : Fin n, (∏ b : {b : Fin n // a < b}, g a b).totalDegree := by
          simpa using (MvPolynomial.totalDegree_finsetProd
            (Finset.univ : Finset (Fin n))
            (fun a => ∏ b : {b : Fin n // a < b}, g a b))
    _ ≤ ∑ a : Fin n, ∑ b : {b : Fin n // a < b}, (g a b).totalDegree := by
          apply Finset.sum_le_sum
          intro a ha
          simpa using (MvPolynomial.totalDegree_finsetProd
            (Finset.univ : Finset {b : Fin n // a < b}) (fun b => g a b))
    _ ≤ ∑ a : Fin n, ∑ _b : {b : Fin n // a < b}, 1 := by
          apply Finset.sum_le_sum
          intro a ha
          apply Finset.sum_le_sum
          intro b hb
          exact hg a b b.property
    _ = Fintype.card (SymmetrizerPairIndex n) := by
          simp [SymmetrizerPairIndex, Fintype.card_sigma]

private theorem symmetrizerAlternant_totalDegree_le [CharZero F] {n : ℕ} (t : F) :
    (symmetrizerAlternantPolynomial (n := n) t).totalDegree ≤
      Fintype.card (SymmetrizerPairIndex n) := by
  classical
  rw [symmetrizerAlternantPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  calc
    (MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : F) *
        pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
          MvPolynomial.X (σ b))).totalDegree
        ≤ (MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : F)).totalDegree +
          (pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
            MvPolynomial.X (σ b))).totalDegree := by
            exact MvPolynomial.totalDegree_mul _ _
    _ = (pairProduct (fun a b => MvPolynomial.C t * MvPolynomial.X (σ a) -
          MvPolynomial.X (σ b))).totalDegree := by
            rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ Fintype.card (SymmetrizerPairIndex n) := by
          apply symmetrizerPairProduct_degree_le
          intro a b hab
          calc
            (MvPolynomial.C t * MvPolynomial.X (σ a) -
                MvPolynomial.X (σ b)).totalDegree
                ≤ max (MvPolynomial.C t * MvPolynomial.X (σ a)).totalDegree
                    (MvPolynomial.X (σ b)).totalDegree :=
                      MvPolynomial.totalDegree_sub _ _
            _ ≤ 1 := by
              apply max_le
              · calc
                  (MvPolynomial.C t * MvPolynomial.X (σ a)).totalDegree
                      ≤ (MvPolynomial.C t).totalDegree +
                          (MvPolynomial.X (σ a)).totalDegree :=
                            MvPolynomial.totalDegree_mul _ _
                  _ = 1 := by simp
              · simp

private theorem symmetrizerVandermonde_totalDegree [CharZero F] {n : ℕ} :
    (symmetrizerVandermondePolynomial (F := F) (n := n)).totalDegree =
      Fintype.card (SymmetrizerPairIndex n) := by
  classical
  rw [← symmetrizerVandermondePairProduct_eq (F := F) (n := n)]
  unfold symmetrizerVandermondePairProduct
  rw [totalDegree_finsetProd_eq_sum]
  · have hfactor (p : SymmetrizerPairIndex n) :
        (MvPolynomial.X p.1 - MvPolynomial.X p.2.1 : MvPolynomial (Fin n) F).totalDegree = 1 :=
      paper_difference_factor_totalDegree (F := F) p.1 p.2.1 p.2.2.ne
    simp_rw [hfactor]
    simp [SymmetrizerPairIndex, Fintype.card_sigma]
  · intro p hp
    exact (paper_difference_factor_irreducible (F := F) p.1 p.2.1 p.2.2.ne).ne_zero

private theorem symmetrizerVandermonde_ne_zero {n : ℕ} :
    symmetrizerVandermondePolynomial (F := F) (n := n) ≠ 0 := by
  classical
  rw [← symmetrizerVandermondePairProduct_eq (F := F) (n := n)]
  unfold symmetrizerVandermondePairProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (paper_difference_factor_irreducible (F := F) p.1 p.2.1 p.2.2.ne).ne_zero

/-- The quotient left by alternation and degree comparison is a scalar,
as in the first part of the source proof. -/
noncomputable def symmetrizerAlternantScalarQuotient [CharZero F] {n : ℕ} (t : F) :
    MvPolynomial (Fin n) F :=
  Classical.choose (symmetrizerAlternant_vandermonde_dvd (F := F) (n := n) t)

theorem symmetrizerAlternantScalarQuotient_spec [CharZero F] {n : ℕ} (t : F) :
    symmetrizerAlternantPolynomial (n := n) t =
      symmetrizerVandermondePolynomial (F := F) (n := n) *
        symmetrizerAlternantScalarQuotient (n := n) t := by
  exact Classical.choose_spec
    (symmetrizerAlternant_vandermonde_dvd (F := F) (n := n) t)

theorem symmetrizerAlternantScalarQuotient_is_constant [CharZero F] {n : ℕ}
    (t : F) : ∃ c : F,
      symmetrizerAlternantScalarQuotient (n := n) t =
        MvPolynomial.C (R := F) (σ := Fin n) c := by
  classical
  let q := symmetrizerAlternantScalarQuotient (F := F) (n := n) t
  have hfactor : symmetrizerAlternantPolynomial (n := n) t =
      symmetrizerVandermondePolynomial (F := F) (n := n) * q := by
    exact symmetrizerAlternantScalarQuotient_spec (F := F) t
  have hbound := symmetrizerAlternant_totalDegree_le (F := F) (n := n) t
  by_cases hq0 : q = 0
  · exact ⟨0, by simp [q, hq0]⟩
  · rw [hfactor, MvPolynomial.totalDegree_mul_of_isDomain
      (symmetrizerVandermonde_ne_zero (F := F) (n := n)) hq0] at hbound
    rw [symmetrizerVandermonde_totalDegree (F := F) (n := n)] at hbound
    have hdegq : q.totalDegree = 0 := Nat.eq_zero_of_le_zero (by omega)
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdegq
    exact ⟨q.coeff 0, by simpa [q] using hdegq⟩

/-- The scalar left after the alternant is divided by the Vandermonde.
The zero evaluation is only a way to name the constant quotient; the source
proof determines it by the zero-variable recurrence below. -/
noncomputable def symmetrizerAlternantScalar [CharZero F] {n : ℕ} (t : F) : F :=
  MvPolynomial.eval (fun _ : Fin n => 0)
    (symmetrizerAlternantScalarQuotient (n := n) t)

theorem symmetrizerAlternantScalarQuotient_eq_C [CharZero F] {n : ℕ} (t : F) :
    symmetrizerAlternantScalarQuotient (n := n) t =
      MvPolynomial.C (symmetrizerAlternantScalar (n := n) t) := by
  obtain ⟨c, hc⟩ := symmetrizerAlternantScalarQuotient_is_constant (n := n) t
  have heval : symmetrizerAlternantScalar (n := n) t = c := by
    dsimp [symmetrizerAlternantScalar]
    rw [hc]
    simp
  rw [heval]
  exact hc

theorem eval_symmetrizerVandermondePolynomial {n : ℕ} (z : Fin n → F) :
    MvPolynomial.eval z symmetrizerVandermondePolynomial =
      pairProduct (fun a b => z a - z b) := by
  unfold symmetrizerVandermondePolynomial pairProduct
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro b hb
  by_cases h : a < b <;> simp [h]

theorem symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde
    [CharZero F] {n : ℕ} (t : F) :
    symmetrizerAlternantPolynomial (n := n) t =
      MvPolynomial.C (symmetrizerAlternantScalar (n := n) t) *
        symmetrizerVandermondePolynomial (F := F) (n := n) := by
  rw [symmetrizerAlternantScalarQuotient_spec,
    symmetrizerAlternantScalarQuotient_eq_C]
  ring

private theorem pairProduct_div {n : ℕ} (f g : Fin n → Fin n → F) :
    pairProduct (fun a b => f a b / g a b) = pairProduct f / pairProduct g := by
  rw [pairProduct_subtype, pairProduct_subtype, pairProduct_subtype]
  calc
    (∏ a : Fin n, ∏ b : {b : Fin n // a < b}, f a b / g a b) =
        ∏ a : Fin n, ((∏ b : {b : Fin n // a < b}, f a b) /
          ∏ b : {b : Fin n // a < b}, g a b) := by
            apply Finset.prod_congr rfl
            intro a ha
            exact Finset.prod_div_distrib (s := Finset.univ)
              (f := fun b : {b : Fin n // a < b} => f a b)
              (g := fun b : {b : Fin n // a < b} => g a b)
    _ = (∏ a : Fin n, ∏ b : {b : Fin n // a < b}, f a b) /
          ∏ a : Fin n, ∏ b : {b : Fin n // a < b}, g a b := by
            exact Finset.prod_div_distrib (s := Finset.univ)
              (f := fun a : Fin n => ∏ b : {b : Fin n // a < b}, f a b)
              (g := fun a : Fin n => ∏ b : {b : Fin n // a < b}, g a b)

private theorem pairProduct_difference_ne_zero {n : ℕ} (z : Fin n → F)
    (hz : Function.Injective z) : pairProduct (fun a b => z a - z b) ≠ 0 := by
  rw [pairProduct_subtype]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  apply sub_ne_zero.mpr
  intro h
  exact (ne_of_lt b.property) (hz h)

/-- The paper's reduction of the type A symmetrizer to the alternating
polynomial numerator divided by the Vandermonde. This is the denominator
sign step preceding the polynomial identity `A_n=V_n Δ_n`. -/
theorem symmetrizer_eq_alternant_div {n : ℕ} (z : Fin n → F) (t : F)
    (hz : Function.Injective z) :
    (∑ σ : Equiv.Perm (Fin n), pairProduct (fun a b =>
      (t * z (σ a) - z (σ b)) / (z (σ a) - z (σ b)))) =
      MvPolynomial.eval z (symmetrizerAlternantPolynomial t) /
        MvPolynomial.eval z symmetrizerVandermondePolynomial := by
  classical
  let Δ := pairProduct (fun a b => z a - z b)
  have hΔ : Δ ≠ 0 := pairProduct_difference_ne_zero z hz
  have hsign2 (σ : Equiv.Perm (Fin n)) :
      ((Equiv.Perm.sign σ : ℤ) : F)^2 = 1 := by
    have h : Equiv.Perm.sign σ * Equiv.Perm.sign σ = 1 := by
      rw [← Equiv.Perm.sign_mul]
      simp
    have hz := congrArg Units.val h
    simp only [Units.val_mul, Units.val_one] at hz
    have hf := congrArg (Int.castRingHom F) hz
    rw [map_mul, map_one] at hf
    rw [pow_two]
    exact hf
  have hterm (σ : Equiv.Perm (Fin n)) :
      pairProduct (fun a b =>
        (t * z (σ a) - z (σ b)) / (z (σ a) - z (σ b))) =
        (((Equiv.Perm.sign σ : ℤ) : F) *
          pairProduct (fun a b => t * z (σ a) - z (σ b))) / Δ := by
    rw [pairProduct_div, pairProduct_difference_permutation]
    have hsquare := hsign2 σ
    have hs : ((Equiv.Perm.sign σ : ℤ) : F) ≠ 0 := by
      intro hzero
      rw [hzero] at hsquare
      norm_num at hsquare
    change pairProduct (fun a b => t * z (σ a) - z (σ b)) /
      (((Equiv.Perm.sign σ : ℤ) : F) * Δ) =
        (((Equiv.Perm.sign σ : ℤ) : F) *
          pairProduct (fun a b => t * z (σ a) - z (σ b))) / Δ
    field_simp [hΔ, hs]
    rw [hsquare]
    ring
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        (((Equiv.Perm.sign σ : ℤ) : F) *
          pairProduct (fun a b => t * z (σ a) - z (σ b)) / Δ) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hterm σ
    _ = (∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : F) *
            pairProduct (fun a b => t * z (σ a) - z (σ b))) / Δ := by
          rw [Finset.sum_div]
    _ = MvPolynomial.eval z (symmetrizerAlternantPolynomial t) /
        MvPolynomial.eval z symmetrizerVandermondePolynomial := by
          rw [eval_symmetrizerAlternantPolynomial, eval_symmetrizerVandermondePolynomial]

theorem pairProduct_succ {M : Type*} [CommMonoid M] {n : ℕ}
    (f : Fin (n+1) → Fin (n+1) → M) :
    pairProduct f = (∏ b : Fin n, f 0 b.succ) *
      pairProduct (fun a b : Fin n => f a.succ b.succ) := by
  classical
  unfold pairProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, lt_self_iff_false, ite_false, one_mul,
    Fin.succ_pos, ite_true, Fin.not_lt_zero, Fin.succ_lt_succ_iff]

theorem symmetrizerVandermondePolynomial_zeroHead {n : ℕ}
    (z : Fin (n+1) → F) :
    MvPolynomial.eval (Fin.cons (0 : F) z)
        (symmetrizerVandermondePolynomial (F := F) (n := n+2)) =
      (-1 : F)^(n+1) * (∏ j : Fin (n+1), z j) *
        MvPolynomial.eval z
          (symmetrizerVandermondePolynomial (F := F) (n := n+1)) := by
  rw [eval_symmetrizerVandermondePolynomial, pairProduct_succ]
  have hhead : (∏ j : Fin (n+1), ((0 : F) - z j)) =
      (-1 : F)^(n+1) * (∏ j : Fin (n+1), z j) := by
    calc
      (∏ j : Fin (n+1), ((0 : F) - (z j))) =
          ∏ j : Fin (n+1), ((-1 : F) * z j) := by
            apply Finset.prod_congr rfl
            intro j hj
            ring
      _ = (∏ j : Fin (n+1), (-1 : F)) * ∏ j : Fin (n+1), z j :=
          Finset.prod_mul_distrib
      _ = (-1 : F)^(n+1) * ∏ j : Fin (n+1), z j := by simp
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hhead, ← eval_symmetrizerVandermondePolynomial]

private def symmetrizerZeroHeadSubst {n : ℕ} :
    MvPolynomial (Fin (n+2)) F →+* MvPolynomial (Fin (n+1)) F :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : F →+* MvPolynomial (Fin (n+1)) F)
    (Fin.cons (α := fun _ : Fin (n+2) => MvPolynomial (Fin (n+1)) F)
      (0 : MvPolynomial (Fin (n+1)) F)
      (fun i : Fin (n+1) => MvPolynomial.X i))

theorem symmetrizerAlternantPolynomial_zeroHead_subst [CharZero F]
    {n : ℕ} (t : F) :
    symmetrizerZeroHeadSubst (F := F) (n := n)
        (symmetrizerAlternantPolynomial (n := n+2) t) =
      MvPolynomial.C
        ((-1 : F)^(n+1) * (∑ p ∈ Finset.range (n+2), t^p)) *
        (∏ j : Fin (n+1), MvPolynomial.X j) *
        symmetrizerAlternantPolynomial (n := n+1) t := by
  apply MvPolynomial.funext
  intro z
  let f : Fin (n+2) → MvPolynomial (Fin (n+1)) F :=
    Fin.cons (α := fun _ : Fin (n+2) => MvPolynomial (Fin (n+1)) F)
      0
    (fun i : Fin (n+1) => MvPolynomial.X i)
  change MvPolynomial.eval z
      (MvPolynomial.eval₂ (MvPolynomial.C) f
        (symmetrizerAlternantPolynomial (n := n+2) t)) = _
  rw [← MvPolynomial.eval_assoc f z
    (symmetrizerAlternantPolynomial (n := n+2) t)]
  have hcomp : (MvPolynomial.eval z) ∘ f = Fin.cons (0 : F) z := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [f]
    · intro j
      simp [f]
  rw [hcomp, symmetrizerAlternantPolynomial_zeroHead]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]

theorem symmetrizerVandermondePolynomial_zeroHead_subst [CharZero F]
    {n : ℕ} :
    symmetrizerZeroHeadSubst (F := F) (n := n)
        (symmetrizerVandermondePolynomial (F := F) (n := n+2)) =
      MvPolynomial.C ((-1 : F)^(n+1)) *
        (∏ j : Fin (n+1), MvPolynomial.X j) *
        symmetrizerVandermondePolynomial (F := F) (n := n+1) := by
  apply MvPolynomial.funext
  intro z
  let f : Fin (n+2) → MvPolynomial (Fin (n+1)) F :=
    Fin.cons (α := fun _ : Fin (n+2) => MvPolynomial (Fin (n+1)) F)
      0
    (fun i : Fin (n+1) => MvPolynomial.X i)
  change MvPolynomial.eval z
      (MvPolynomial.eval₂ (MvPolynomial.C) f
        (symmetrizerVandermondePolynomial (F := F) (n := n+2))) = _
  rw [← MvPolynomial.eval_assoc f z
    (symmetrizerVandermondePolynomial (F := F) (n := n+2))]
  have hcomp : (MvPolynomial.eval z) ∘ f = Fin.cons (0 : F) z := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [f]
    · intro j
      simp [f]
  rw [hcomp, symmetrizerVandermondePolynomial_zeroHead]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]

/-- The scalar quotient recurrence obtained by comparing the source's
zero-variable specializations of the alternant and Vandermonde. -/
theorem symmetrizerAlternantScalar_succ [CharZero F] (n : ℕ) (t : F) :
    symmetrizerAlternantScalar (n := n+2) t =
      (∑ p ∈ Finset.range (n+2), t^p) *
        symmetrizerAlternantScalar (n := n+1) t := by
  let Xprod : MvPolynomial (Fin (n+1)) F :=
    ∏ j : Fin (n+1), MvPolynomial.X j
  let D := symmetrizerVandermondePolynomial (F := F) (n := n+1)
  let K : MvPolynomial (Fin (n+1)) F :=
    MvPolynomial.C ((-1 : F)^(n+1)) * Xprod * D
  have hfactorN := symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde
    (F := F) (n := n+2) t
  have hfactorPrev := symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde
    (F := F) (n := n+1) t
  have hsubstN :
      symmetrizerZeroHeadSubst (F := F) (n := n)
          (symmetrizerAlternantPolynomial (n := n+2) t) =
        MvPolynomial.C (symmetrizerAlternantScalar (n := n+2) t) *
          symmetrizerZeroHeadSubst (F := F) (n := n)
            (symmetrizerVandermondePolynomial (F := F) (n := n+2)) := by
    rw [hfactorN]
    simp [symmetrizerZeroHeadSubst]
  have hscalarEq :
      MvPolynomial.C (symmetrizerAlternantScalar (n := n+2) t) * K =
        MvPolynomial.C
            ((∑ p ∈ Finset.range (n+2), t^p) *
              symmetrizerAlternantScalar (n := n+1) t) * K := by
    dsimp [K, Xprod, D] at *
    rw [symmetrizerVandermondePolynomial_zeroHead_subst] at hsubstN
    rw [symmetrizerAlternantPolynomial_zeroHead_subst] at hsubstN
    rw [hfactorPrev] at hsubstN
    rw [← hsubstN]
    rw [MvPolynomial.C_mul, MvPolynomial.C_mul]
    ring
  have hK : K ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact MvPolynomial.C_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      · dsimp [Xprod]
        apply Finset.prod_ne_zero_iff.mpr
        intro j hj
        exact MvPolynomial.X_ne_zero j
    · exact symmetrizerVandermonde_ne_zero (F := F) (n := n+1)
  have hC := mul_right_cancel₀ hK hscalarEq
  exact MvPolynomial.C_injective _ _ hC

theorem symmetrizerAlternantScalar_zero [CharZero F] (t : F) :
    symmetrizerAlternantScalar (n := 0) t = 1 := by
  have h := symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde
    (F := F) (n := 0) t
  have hC : MvPolynomial.C (R := F) (σ := Fin 0) (1 : F) =
      MvPolynomial.C (R := F) (σ := Fin 0)
        (symmetrizerAlternantScalar (n := 0) t) := by
    simpa [symmetrizerAlternantPolynomial, symmetrizerVandermondePolynomial,
      pairProduct] using h
  exact MvPolynomial.C_injective (Fin 0) F hC.symm

theorem symmetrizerAlternantScalar_one [CharZero F] (t : F) :
    symmetrizerAlternantScalar (n := 1) t = 1 := by
  have h := symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde
    (F := F) (n := 1) t
  have hC : MvPolynomial.C (R := F) (σ := Fin 1) (1 : F) =
      MvPolynomial.C (R := F) (σ := Fin 1)
        (symmetrizerAlternantScalar (n := 1) t) := by
    simpa [symmetrizerAlternantPolynomial, symmetrizerVandermondePolynomial,
      pairProduct] using h
  exact MvPolynomial.C_injective (Fin 1) F hC.symm

theorem symmetrizerAlternantScalar_eq_Vn [CharZero F] {n : ℕ} (t : F) :
    symmetrizerAlternantScalar (n := n) t = ExternalHL.Vn n t := by
  induction n with
  | zero => simp [symmetrizerAlternantScalar_zero, ExternalHL.Vn]
  | succ n ih =>
    cases n with
    | zero => simp [symmetrizerAlternantScalar_one, ExternalHL.Vn]
    | succ n =>
      rw [symmetrizerAlternantScalar_succ n t, Vn_succ (n+1) t, ih]

theorem symmetrizerAlternantPolynomial_eq_Vn_mul_vandermonde
    [CharZero F] {n : ℕ} (t : F) :
    symmetrizerAlternantPolynomial (n := n) t =
      MvPolynomial.C (ExternalHL.Vn n t) *
        symmetrizerVandermondePolynomial (F := F) (n := n) := by
  rw [symmetrizerAlternantPolynomial_eq_scalar_mul_vandermonde,
    symmetrizerAlternantScalar_eq_Vn]

/-- The paper's unnumbered type A symmetrizer identity immediately preceding
(2.2), proved by the source's alternant, Vandermonde, degree, and zero-variable
recurrence argument. -/
theorem symmetrizer [CharZero F] {n : ℕ} (z : Fin n → F) (t : F)
    (hz : Function.Injective z) :
    (∑ σ : Equiv.Perm (Fin n), pairProduct (fun a b =>
      (t * z (σ a) - z (σ b)) / (z (σ a) - z (σ b)))) = ExternalHL.Vn n t := by
  have hΔ : MvPolynomial.eval z
      (symmetrizerVandermondePolynomial (F := F) (n := n)) ≠ 0 := by
    rw [eval_symmetrizerVandermondePolynomial]
    exact pairProduct_difference_ne_zero z hz
  rw [symmetrizer_eq_alternant_div z t hz,
    symmetrizerAlternantPolynomial_eq_Vn_mul_vandermonde]
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  field_simp [hΔ]

end
end AffineDualJT
