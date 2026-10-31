import AffineDualJT.AlternantPaperRoute
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-!
# Divisibility steps in the proof of Lemma 2.1

The paper checks factors by regarding each alternant as a polynomial in one
variable over the ring in the remaining variables. The three alternants now
have reciprocal and difference factors proved for arbitrary distinct variable
pairs by this univariate root, Gauss-lemma, and variable-renaming route.
The Ct and B₋ row factors are also proved by the finite geometric sums in the
paper and extracted from their determinants by multilinearity. Product
aggregation, degree comparison, and normalization remain in `FiniteWeyl`.
-/

namespace AffineDualJT
open Polynomial

noncomputable section

variable {F : Type*} [Field F]

/-- The Leibniz expansion gives a total-degree bound by the sum of the
column bounds. This is the degree comparison used in the paper's proof of
Lemma 2.1. -/
theorem paper_det_totalDegree_le_sum_column_bounds {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) F))
    (d : Fin n → ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ d j) :
    M.det.totalDegree ≤ ∑ j : Fin n, d j := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  calc
    (Equiv.Perm.sign σ • ∏ i : Fin n, M (σ i) i).totalDegree
        ≤ (∏ i : Fin n, M (σ i) i).totalDegree :=
          MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (M (σ i) i).totalDegree := by
          simpa using (MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin n))
            (fun i => M (σ i) i))
    _ ≤ ∑ i : Fin n, d i :=
          Finset.sum_le_sum fun i hi => hM (σ i) i

theorem paper_fColumn_totalDegree_le {n : ℕ} (t : F) (a r : Fin n) :
    (fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)).totalDegree
      ≤ n + r.val - 1 := by
  by_cases hr : r.val = 0
  · simp [fColumn, hr]
  · rw [fColumn, ite_eq_right hr]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
      omega
    · calc
        (MvPolynomial.C t ^ r.val * MvPolynomial.X a ^ (n + r.val - 1)).totalDegree
            ≤ (MvPolynomial.C t ^ r.val).totalDegree +
                (MvPolynomial.X a ^ (n + r.val - 1)).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
        _ = n + r.val - 1 := by
          rw [← map_pow (MvPolynomial.C : F →+* MvPolynomial (Fin n) F),
            MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
          simp

theorem paper_ctColumn_totalDegree_le {n : ℕ} (t : F) (a r : Fin n) :
    (ctAlternantColumn (MvPolynomial.C t) r
      (MvPolynomial.X a : MvPolynomial (Fin n) F)).totalDegree ≤ n + r.val + 1 := by
  rw [ctAlternantColumn]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
    omega
  · calc
      (MvPolynomial.C t ^ (r.val + 1) * MvPolynomial.X a ^ (n + r.val + 1)).totalDegree
          ≤ (MvPolynomial.C t ^ (r.val + 1)).totalDegree +
              (MvPolynomial.X a ^ (n + r.val + 1)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = n + r.val + 1 := by
        rw [← map_pow (MvPolynomial.C : F →+* MvPolynomial (Fin n) F),
          MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
        simp

theorem paper_bminusColumn_totalDegree_le {n : ℕ} (τ : F) (a r : Fin n) :
    (bminusAlternantColumn (MvPolynomial.C τ) r
      (MvPolynomial.X a : MvPolynomial (Fin n) F)).totalDegree ≤ n + r.val := by
  rw [bminusAlternantColumn]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp
    omega
  · calc
      (MvPolynomial.C τ ^ (2 * r.val + 1) * MvPolynomial.X a ^ (n + r.val)).totalDegree
          ≤ (MvPolynomial.C τ ^ (2 * r.val + 1)).totalDegree +
              (MvPolynomial.X a ^ (n + r.val)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = n + r.val := by
        rw [← map_pow (MvPolynomial.C : F →+* MvPolynomial (Fin n) F),
          MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
        simp

private def paperFinUpperEquiv (n : ℕ) (a : Fin n) :
    Fin (n - (a.val + 1)) ≃ {b : Fin n // a < b} where
  toFun i := ⟨⟨a.val + 1 + i.val, by have := i.isLt; omega⟩, by change a.val < a.val + 1 + i.val; omega⟩
  invFun b := ⟨b.1.val - (a.val + 1), by omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv b := by apply Subtype.ext; apply Fin.ext; dsimp; omega

theorem paper_fin_upper_card (n : ℕ) (a : Fin n) :
    Fintype.card {b : Fin n // a < b} = n - (a.val + 1) := by
  classical
  rw [← Fintype.card_fin (n - (a.val + 1)), Fintype.card_congr (paperFinUpperEquiv n a)]

theorem paper_basic_column_degree_sum (n : ℕ) :
    (∑ r : Fin n, (n + r.val - 1)) = 3 * (n * (n - 1) / 2) := by
  classical
  have hsum : (∑ r : Fin n, (n + r.val - 1)) =
      ∑ i ∈ Finset.range n, (n + i - 1) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => n + i - 1) n)
  rw [hsum]
  rw [show (∑ i ∈ Finset.range n, (n + i - 1)) =
      ∑ i ∈ Finset.range n, ((n - 1) + i) by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        omega]
  have hsplit : (∑ i ∈ Finset.range n, ((n - 1) + i)) =
      (∑ _i ∈ Finset.range n, (n - 1)) + (∑ i ∈ Finset.range n, i) := by
    change (∑ i ∈ Finset.range n, ((fun _ : ℕ => n - 1) i + (fun i => i) i)) = _
    exact Finset.sum_add_distrib
  rw [hsplit]
  have hc : (∑ _i ∈ Finset.range n, (n - 1)) = n * (n - 1) := by simp
  have hid : (∑ i ∈ Finset.range n, i) = n * (n - 1) / 2 :=
    Finset.sum_range_id n
  rw [hc, hid]
  have heven := Nat.even_mul_pred_self n
  have hdiv : 2 ∣ n * (n - 1) := heven.two_dvd
  have hmul : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdiv)
  nlinarith [hmul]

theorem paper_ct_column_degree_sum (n : ℕ) :
    (∑ r : Fin n, (n + r.val + 1)) = 3 * (n * (n - 1) / 2) + 2 * n := by
  classical
  have hsum : (∑ r : Fin n, (n + r.val + 1)) =
      ∑ i ∈ Finset.range n, (n + i + 1) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => n + i + 1) n)
  rw [hsum]
  rw [show (∑ i ∈ Finset.range n, (n + i + 1)) =
      ∑ i ∈ Finset.range n, ((n + 1) + i) by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        omega]
  have hsplit : (∑ i ∈ Finset.range n, ((n + 1) + i)) =
      (∑ _i ∈ Finset.range n, (n + 1)) + (∑ i ∈ Finset.range n, i) := by
    change (∑ i ∈ Finset.range n, ((fun _ : ℕ => n + 1) i + (fun i => i) i)) = _
    exact Finset.sum_add_distrib
  rw [hsplit]
  have hc : (∑ _i ∈ Finset.range n, (n + 1)) = n * (n + 1) := by simp
  have hid : (∑ i ∈ Finset.range n, i) = n * (n - 1) / 2 :=
    Finset.sum_range_id n
  rw [hc, hid]
  have heven := Nat.even_mul_pred_self n
  have hdiv : 2 ∣ n * (n - 1) := heven.two_dvd
  have hmul : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdiv)
  have hnn : n * (n + 1) = n * (n - 1) + 2 * n := by
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : n - 1 + 1 = n := by omega
      nlinarith
  nlinarith [hmul, hnn]

theorem paper_bminus_column_degree_sum (n : ℕ) :
    (∑ r : Fin n, (n + r.val)) = 3 * (n * (n - 1) / 2) + n := by
  classical
  have hsum : (∑ r : Fin n, (n + r.val)) =
      ∑ i ∈ Finset.range n, (n + i) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => n + i) n)
  rw [hsum]
  have hsplit : (∑ i ∈ Finset.range n, (n + i)) =
      (∑ _i ∈ Finset.range n, n) + (∑ i ∈ Finset.range n, i) := by
    change (∑ i ∈ Finset.range n, ((fun _ : ℕ => n) i + (fun i => i) i)) = _
    exact Finset.sum_add_distrib
  rw [hsplit]
  have hc : (∑ _i ∈ Finset.range n, n) = n * n := by simp
  have hid : (∑ i ∈ Finset.range n, i) = n * (n - 1) / 2 := Finset.sum_range_id n
  rw [hc, hid]
  have heven := Nat.even_mul_pred_self n
  have hdiv : 2 ∣ n * (n - 1) := heven.two_dvd
  have hmul : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdiv)
  have hnn : n * n = n * (n - 1) + n := by
    by_cases hn : n = 0
    · simp [hn]
    · have hsub : n - 1 + 1 = n := by omega
      nlinarith
  nlinarith [hmul, hnn]

private theorem paper_one_sub_pow_geom {R : Type*} [CommRing R] (x : R) :
    ∀ k : ℕ, 1 - x^k = (1 - x) * ∑ i ∈ Finset.range k, x^i
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, Finset.sum_range_succ]
      calc
        1 - x ^ k * x = (1 - x ^ k) + x ^ k - x ^ (k+1) := by ring
        _ = (1 - x) * (∑ i ∈ Finset.range k, x ^ i) + x ^ k - x ^ (k+1) := by
          rw [← paper_one_sub_pow_geom x k]
        _ = (1 - x) * (∑ i ∈ Finset.range k, x ^ i + x ^ k) := by ring

private theorem paper_one_add_odd_pow_geom {R : Type*} [CommRing R] (x : R) :
    ∀ k : ℕ, (1 + x) * ∑ i ∈ Finset.range k, (-x)^i = 1 - (-x)^k
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (1 + x) * ((∑ i ∈ Finset.range k, (-x)^i) + (-x)^k) =
            (1 + x) * (∑ i ∈ Finset.range k, (-x)^i) + (1+x)*(-x)^k := by ring
        _ = (1 - (-x)^k) + (1+x)*(-x)^k := by rw [paper_one_add_odd_pow_geom x k]
        _ = 1 - (-x)^k * (-x) := by ring

def paperCtRowQuotient {R : Type*} [CommRing R] {n : ℕ} (t : R) (r : Fin n) (z : R) : R :=
  z^(n-(r.val+1)) * ∑ i ∈ Finset.range (r.val+1), (t*z^2)^i

theorem paper_ct_column_extra_row_factor {R : Type*} [CommRing R] {n : ℕ} (t z : R) (r : Fin n) :
    ctAlternantColumn t r z = (1-t*z^2) * paperCtRowQuotient t r z := by
  let k := r.val + 1
  let m := n - k
  have hk : k ≤ n := by dsimp [k]; omega
  have hexp : n + r.val + 1 = m + 2*k := by dsimp [m,k]; omega
  have hpow : z^(n+r.val+1) = z^m * (z^2)^k := by
    rw [hexp, pow_add, ← pow_mul]
  have hgeom := paper_one_sub_pow_geom (t*z^2) k
  have hbase : (t*z^2)^k = t^k * (z^2)^k := by rw [mul_pow]
  simp only [ctAlternantColumn, paperCtRowQuotient]
  rw [hpow]
  calc
      z ^ (n - (r.val + 1)) - t ^ (r.val + 1) * (z ^ (n - (r.val + 1)) * (z ^ 2) ^ (r.val + 1)) =
      z ^ (n - (r.val + 1)) * (1 - (t*z^2)^(r.val+1)) := by
        rw [hbase]
        ring
    _ = z ^ (n - (r.val + 1)) *
        ((1-t*z^2) * ∑ i ∈ Finset.range (r.val+1), (t*z^2)^i) := by rw [hgeom]
    _ = (1-t*z^2) * paperCtRowQuotient t r z := by
        unfold paperCtRowQuotient
        ring

def paperBminusRowQuotient {R : Type*} [CommRing R] {n : ℕ} (τ : R) (r : Fin n) (z : R) : R :=
  z^(n-(r.val+1)) * ∑ i ∈ Finset.range (2*r.val+1), (-τ*z)^i

theorem paper_bminus_column_extra_row_factor {R : Type*} [CommRing R] {n : ℕ} (τ z : R) (r : Fin n) :
    bminusAlternantColumn τ r z = (1+τ*z) * paperBminusRowQuotient τ r z := by
  let k := 2*r.val+1
  let m := n-(r.val+1)
  have hexp : n + r.val = m+k := by dsimp [m,k]; omega
  have hpow : z^(n+r.val) = z^m*z^k := by rw [hexp, pow_add]
  have hgeom := paper_one_add_odd_pow_geom (τ*z) k
  have hbase : (τ*z)^k = τ^k*z^k := by rw [mul_pow]
  have hk : (- (τ*z))^k = -(τ*z)^k := by
    dsimp [k]
    rw [pow_succ]
    have heven : (-(τ*z))^(2*r.val) = (τ*z)^(2*r.val) := by
      calc
        (-(τ*z))^(2*r.val) = ((-(τ*z))^2)^r.val := by
          rw [pow_mul]
        _ = ((τ*z)^2)^r.val := by rw [show (-(τ*z))^2 = (τ*z)^2 by ring]
        _ = (τ*z)^(2*r.val) := by rw [pow_mul]
    rw [heven]
    rw [pow_succ]
    ring
  rw [← neg_mul] at hgeom
  have hk' : (-τ*z)^k = -(τ*z)^k := by
    rw [show -τ*z = -(τ*z) by ring]
    exact hk
  simp only [bminusAlternantColumn, paperBminusRowQuotient]
  rw [hpow]
  calc
    z ^ (n-(r.val+1)) + τ^(2*r.val+1) * (z^(n-(r.val+1))*z^(2*r.val+1)) =
      z^(n-(r.val+1)) * (1 + (τ*z)^(2*r.val+1)) := by
        rw [hbase]
        ring
    _ = z^(n-(r.val+1)) *
        ((1+τ*z) * ∑ i ∈ Finset.range (2*r.val+1), (-τ*z)^i) := by
          rw [hgeom, hk']
          ring
    _ = (1+τ*z) * paperBminusRowQuotient τ r z := by
        unfold paperBminusRowQuotient
        ring

/-- Once the single-column identities are assembled into matrices, multilinearity
of the determinant extracts all of the paper's additional row factors. -/
theorem paper_ct_determinant_extra_row_factors {R : Type*} [CommRing R] {n : ℕ}
    (t : R) (z : Fin n → R) :
    (Matrix.of fun a r : Fin n => ctAlternantColumn t r (z a)).det =
      (∏ a : Fin n, (1-t*(z a)^2)) *
        (Matrix.of fun a r : Fin n => paperCtRowQuotient t r (z a)).det := by
  rw [show (Matrix.of fun a r : Fin n => ctAlternantColumn t r (z a)) =
      Matrix.of (fun a r => (1-t*(z a)^2) * paperCtRowQuotient t r (z a)) by
        funext a r
        exact paper_ct_column_extra_row_factor t (z a) r]
  exact Matrix.det_mul_column (fun a => 1-t*(z a)^2)
    (Matrix.of fun a r : Fin n => paperCtRowQuotient t r (z a))

/-- Rowwise extraction of the third alternant's factors `1+τ z_a`. -/
theorem paper_bminus_determinant_extra_row_factors {R : Type*} [CommRing R] {n : ℕ}
    (τ : R) (z : Fin n → R) :
    (Matrix.of fun a r : Fin n => bminusAlternantColumn τ r (z a)).det =
      (∏ a : Fin n, (1+τ*z a)) *
        (Matrix.of fun a r : Fin n => paperBminusRowQuotient τ r (z a)).det := by
  rw [show (Matrix.of fun a r : Fin n => bminusAlternantColumn τ r (z a)) =
      Matrix.of (fun a r => (1+τ*z a) * paperBminusRowQuotient τ r (z a)) by
        funext a r
        exact paper_bminus_column_extra_row_factor τ (z a) r]
  exact Matrix.det_mul_column (fun a => 1+τ*z a)
    (Matrix.of fun a r : Fin n => paperBminusRowQuotient τ r (z a))

def paperBasicAlternantPolynomial {n : ℕ} (t : F) :
    MvPolynomial (Fin n) F :=
  (Matrix.of fun a r : Fin n =>
    fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)).det

abbrev paperAlternantPairIndex (n : ℕ) :=
  Σ a : Fin n, {b : Fin n // a < b}

abbrev paperBasicFactorIndex (n : ℕ) :=
  Σ _p : paperAlternantPairIndex n, Bool

def paperBasicFactor {n : ℕ} (t : F) (i : paperBasicFactorIndex n) :
    MvPolynomial (Fin n) F :=
  if i.2 then
    1 - MvPolynomial.C t * MvPolynomial.X i.1.1 * MvPolynomial.X i.1.2.1
  else MvPolynomial.X i.1.1 - MvPolynomial.X i.1.2.1

def paperBasicFactorProduct {n : ℕ} (t : F) : MvPolynomial (Fin n) F :=
  ∏ i : paperBasicFactorIndex n, paperBasicFactor t i

abbrev paperCtFactorIndex (n : ℕ) := paperBasicFactorIndex n ⊕ Fin n

def paperCtFactor {n : ℕ} (t : F) (i : paperCtFactorIndex n) : MvPolynomial (Fin n) F :=
  match i with
  | Sum.inl p => paperBasicFactor t p
  | Sum.inr a => 1 - MvPolynomial.C t * MvPolynomial.X a ^ 2

def paperCtFactorProduct {n : ℕ} (t : F) : MvPolynomial (Fin n) F :=
  ∏ i : paperCtFactorIndex n, paperCtFactor t i

abbrev paperBminusFactorIndex (n : ℕ) := paperBasicFactorIndex n ⊕ Fin n

def paperBminusFactor {n : ℕ} (τ : F) (i : paperBminusFactorIndex n) :
    MvPolynomial (Fin n) F :=
  match i with
  | Sum.inl p => paperBasicFactor (τ^2) p
  | Sum.inr a => 1 + MvPolynomial.C τ * MvPolynomial.X a

def paperBminusFactorProduct {n : ℕ} (τ : F) : MvPolynomial (Fin n) F :=
  ∏ i : paperBminusFactorIndex n, paperBminusFactor τ i

theorem paper_reciprocal_factor_irreducible {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    Irreducible (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) := by
  let f : MvPolynomial (Fin n) F := -(MvPolynomial.C t * MvPolynomial.X b)
  have hf : f ≠ 0 := by
    simp [f, ht]
  have hif : a ∉ f.vars := by
    simp [f, MvPolynomial.vars_C_mul, ht, hab]
  have hig : a ∉ (1 : MvPolynomial (Fin n) F).vars := by simp
  have hfg : IsRelPrime f (1 : MvPolynomial (Fin n) F) := isRelPrime_one_right
  have hirr := MvPolynomial.irreducible_mul_X_add f 1 a hf hif hig hfg
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) = f * MvPolynomial.X a + 1 by
        dsimp [f]
        ring]
  exact hirr

theorem paper_difference_factor_irreducible {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Irreducible (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F) := by
  have hg : a ∉ (-(MvPolynomial.X b : MvPolynomial (Fin n) F)).vars := by
    simp [hab]
  have hirr := MvPolynomial.irreducible_mul_X_add
    (1 : MvPolynomial (Fin n) F) (-MvPolynomial.X b) a one_ne_zero (by simp) hg
      isRelPrime_one_left
  rw [show (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F) =
      (1 : MvPolynomial (Fin n) F) * MvPolynomial.X a + (-MvPolynomial.X b) by ring]
  exact hirr

theorem paper_sum_factor_irreducible {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Irreducible (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) F) := by
  have hg : a ∉ (MvPolynomial.X b : MvPolynomial (Fin n) F).vars := by
    simp [hab]
  have hirr := MvPolynomial.irreducible_mul_X_add
    (1 : MvPolynomial (Fin n) F) (MvPolynomial.X b) a one_ne_zero (by simp) hg
      isRelPrime_one_left
  rw [show (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) F) =
      (1 : MvPolynomial (Fin n) F) * MvPolynomial.X a + MvPolynomial.X b by ring]
  exact hirr

theorem paper_sum_factor_degreeOf_right {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (MvPolynomial.X a + MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf b = 1 := by
  rw [add_comm, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := b) (by
    simp [MvPolynomial.degreeOf_X_of_ne hab.symm])]
  simp

theorem paper_reciprocal_factor_totalDegree {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).totalDegree = 2 := by
  have htC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr ht
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.X_ne_zero a
  have hXb : (MvPolynomial.X b : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.X_ne_zero b
  have hprod : (MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain (mul_ne_zero htC hXa) hXb,
      MvPolynomial.totalDegree_mul_of_isDomain htC hXa]
    simp
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) =
      -(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) + 1 by ring,
    MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · simp [hprod]
  · simp [hprod]

theorem paper_reciprocal_factor_degreeOf_left {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf a = 1 := by
  have hC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr ht
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero a
  have hXb : (MvPolynomial.X b : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero b
  have hprod : (MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf a = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq (mul_ne_zero hC hXa) hXb,
      MvPolynomial.degreeOf_mul_eq hC hXa]
    simp [MvPolynomial.degreeOf_X_of_ne hab]
  have hneg : (-(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F)).degreeOf a = 1 := by simpa using hprod
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) =
      -(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) + 1 by ring,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := a) (by simp [hneg])]
  exact hneg

theorem paper_reciprocal_factor_degreeOf_right {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf b = 1 := by
  have hC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr ht
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero a
  have hXb : (MvPolynomial.X b : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero b
  have hprod : (MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf b = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq (mul_ne_zero hC hXa) hXb,
      MvPolynomial.degreeOf_mul_eq hC hXa]
    simp [MvPolynomial.degreeOf_X_of_ne hab.symm]
  have hneg : (-(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F)).degreeOf b = 1 := by simpa using hprod
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) =
      -(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) + 1 by ring,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := b) (by simp [hneg])]
  exact hneg

theorem paper_reciprocal_factor_degreeOf_outside {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b x : Fin n) (hxa : x ≠ a) (hxb : x ≠ b) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf x = 0 := by
  have hC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr ht
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero a
  have hXb : (MvPolynomial.X b : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero b
  have hprod : (MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf x = 0 := by
    rw [MvPolynomial.degreeOf_mul_eq (mul_ne_zero hC hXa) hXb,
      MvPolynomial.degreeOf_mul_eq hC hXa]
    simp [MvPolynomial.degreeOf_X_of_ne hxa, MvPolynomial.degreeOf_X_of_ne hxb]
  have hneg : (-(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F)).degreeOf x = 0 := by simpa using hprod
  have hle : (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F).degreeOf x ≤ 0 := by
    rw [show (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
        MvPolynomial (Fin n) F) =
        -(MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) + 1 by ring]
    exact (MvPolynomial.degreeOf_add_le x _ _).trans (by simp [hneg])
  omega

private theorem paper_not_dvd_degreeOf_mismatch {n : ℕ} {p q : MvPolynomial (Fin n) F}
    (x : Fin n) (hp : p.degreeOf x = 1) (hq : q.degreeOf x = 0)
    (hpne : p ≠ 0) (hqne : q ≠ 0) : ¬ p ∣ q := by
  rintro ⟨r, hr⟩
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    exact hqne hr
  rw [hr, MvPolynomial.degreeOf_mul_eq hpne hrne] at hq
  omega

theorem paper_reciprocal_isRelPrime_reciprocal {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b c d : Fin n) (hab : a < b) (hcd : c < d)
    (hne : a ≠ c ∨ b ≠ d) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) (1 - MvPolynomial.C t * MvPolynomial.X c * MvPolynomial.X d) := by
  have hrec := paper_reciprocal_factor_irreducible t ht a b hab.ne
  rw [hrec.isRelPrime_iff_not_dvd]
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h
      exact hne.elim (fun hn => hn hac) (fun hn => hn h)
    apply paper_not_dvd_degreeOf_mismatch b
      (paper_reciprocal_factor_degreeOf_right t ht a b hab.ne)
      (paper_reciprocal_factor_degreeOf_outside t ht c d b (by simpa [hac] using hab.ne.symm)
        (by exact hbd))
      (by
        intro hz
        have hd := paper_reciprocal_factor_totalDegree t ht a b
        rw [hz] at hd
        simp at hd)
      (by
        intro hz
        have hd := paper_reciprocal_factor_totalDegree t ht c d
        rw [hz] at hd
        simp at hd)
  · by_cases had : a = d
    · have hbc : b ≠ c := by
        intro h
        have : c < a := by simpa [had] using hcd
        omega
      have hbd : b ≠ d := by
        intro h
        omega
      apply paper_not_dvd_degreeOf_mismatch b
        (paper_reciprocal_factor_degreeOf_right t ht a b hab.ne)
        (paper_reciprocal_factor_degreeOf_outside t ht c d b hbc hbd)
        (by
          intro hz
          have hd := paper_reciprocal_factor_totalDegree t ht a b
          rw [hz] at hd
          simp at hd)
        (by
          intro hz
          have hd := paper_reciprocal_factor_totalDegree t ht c d
          rw [hz] at hd
          simp at hd)
    · apply paper_not_dvd_degreeOf_mismatch a
        (paper_reciprocal_factor_degreeOf_left t ht a b hab.ne)
        (paper_reciprocal_factor_degreeOf_outside t ht c d a hac had)
        (by
          intro hz
          have hd := paper_reciprocal_factor_totalDegree t ht a b
          rw [hz] at hd
          simp at hd)
        (by
          intro hz
          have hd := paper_reciprocal_factor_totalDegree t ht c d
          rw [hz] at hd
          simp at hd)

theorem paper_difference_factor_totalDegree {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).totalDegree = 1 := by
  have hup : (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).totalDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  have hmem : Finsupp.single a 1 ∈
      (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).support := by
    rw [MvPolynomial.mem_support_iff]
    simp [hab.symm]
  have hlo := MvPolynomial.le_totalDegree hmem
  simpa using le_antisymm hup (by simpa using hlo)

theorem paper_basic_factor_totalDegree {n : ℕ} (t : F) (ht : t ≠ 0)
    (i : paperBasicFactorIndex n) :
    (paperBasicFactor t i).totalDegree = if i.2 then 2 else 1 := by
  classical
  by_cases hi : i.2
  · simpa [paperBasicFactor, hi] using
      paper_reciprocal_factor_totalDegree t ht i.1.1 i.1.2.1
  · simpa [paperBasicFactor, hi] using
      paper_difference_factor_totalDegree i.1.1 i.1.2.1 (ne_of_lt i.1.2.2)

private theorem paper_totalDegree_finsetProd_eq_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) F)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).totalDegree = ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hprod : (∏ i ∈ s, f i) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [MvPolynomial.totalDegree_mul_of_isDomain (hf a (Finset.mem_insert_self a s)) hprod,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem paper_basic_factor_product_totalDegree {n : ℕ} (t : F) (ht : t ≠ 0) :
    (paperBasicFactorProduct (n := n) t).totalDegree =
      ∑ i : paperBasicFactorIndex n, if i.2 then 2 else 1 := by
  classical
  rw [paperBasicFactorProduct, paper_totalDegree_finsetProd_eq_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact paper_basic_factor_totalDegree t ht i
  · intro i hi
    have hd := paper_basic_factor_totalDegree t ht i
    intro hz
    rw [hz] at hd
    cases hbool : i.2 <;> simp [hbool] at hd

theorem paper_basic_factor_degree_sum {n : ℕ} :
    (∑ i : paperBasicFactorIndex n, if i.2 then 2 else 1) =
      3 * Fintype.card (paperAlternantPairIndex n) := by
  classical
  simp only [paperBasicFactorIndex, Fintype.sum_sigma]
  simp
  calc
    (∑ x : Fin n,
        Fintype.card {b : Fin n // x < b} * 3) =
        ∑ x : Fin n,
          3 * Fintype.card {b : Fin n // x < b} := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = 3 * ∑ x : Fin n,
        Fintype.card {b : Fin n // x < b} := by rw [← Finset.mul_sum]

theorem paper_alternant_pairIndex_card {n : ℕ} :
    Fintype.card (paperAlternantPairIndex n) =
      ∑ a : Fin n, Fintype.card {b : Fin n // a < b} := by
  classical
  simp [paperAlternantPairIndex, Fintype.card_sigma]

theorem paper_alternant_pairIndex_card_eq_triangular (n : ℕ) :
    Fintype.card (paperAlternantPairIndex n) = n * (n - 1) / 2 := by
  classical
  rw [paper_alternant_pairIndex_card]
  simp_rw [paper_fin_upper_card]
  have hsum : (∑ a : Fin n, (n - (a.val + 1))) =
      ∑ i ∈ Finset.range n, (n - (i + 1)) := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ => n - (i + 1)) n)
  rw [hsum]
  calc
    (∑ i ∈ Finset.range n, (n - (i + 1))) =
        ∑ i ∈ Finset.range n, (n - 1 - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          omega
    _ = ∑ i ∈ Finset.range n, i := by
          simpa using (Finset.sum_range_reflect (fun i : ℕ => i) n)
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

theorem paper_basic_alternant_totalDegree_le {n : ℕ} (t : F) :
    (Matrix.of fun a r : Fin n =>
      fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)).det.totalDegree
        ≤ 3 * Fintype.card (paperAlternantPairIndex n) := by
  calc
    _ ≤ ∑ r : Fin n, (n + r.val - 1) :=
      paper_det_totalDegree_le_sum_column_bounds _ _ (fun a r => paper_fColumn_totalDegree_le t a r)
    _ = 3 * (n * (n - 1) / 2) := paper_basic_column_degree_sum n
    _ = 3 * Fintype.card (paperAlternantPairIndex n) := by
      rw [paper_alternant_pairIndex_card_eq_triangular]

theorem paper_ct_alternant_totalDegree_le {n : ℕ} (t : F) :
    (Matrix.of fun a r : Fin n =>
      ctAlternantColumn (MvPolynomial.C t) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)).det.totalDegree
        ≤ 3 * Fintype.card (paperAlternantPairIndex n) + 2 * n := by
  calc
    _ ≤ ∑ r : Fin n, (n + r.val + 1) :=
      paper_det_totalDegree_le_sum_column_bounds _ _ (fun a r => paper_ctColumn_totalDegree_le t a r)
    _ = 3 * (n * (n - 1) / 2) + 2 * n := paper_ct_column_degree_sum n
    _ = 3 * Fintype.card (paperAlternantPairIndex n) + 2 * n := by
      rw [paper_alternant_pairIndex_card_eq_triangular]

theorem paper_bminus_alternant_totalDegree_le {n : ℕ} (τ : F) :
    (Matrix.of fun a r : Fin n =>
      bminusAlternantColumn (MvPolynomial.C τ) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)).det.totalDegree
        ≤ 3 * Fintype.card (paperAlternantPairIndex n) + n := by
  calc
    _ ≤ ∑ r : Fin n, (n + r.val) :=
      paper_det_totalDegree_le_sum_column_bounds _ _ (fun a r => paper_bminusColumn_totalDegree_le τ a r)
    _ = 3 * (n * (n - 1) / 2) + n := paper_bminus_column_degree_sum n
    _ = 3 * Fintype.card (paperAlternantPairIndex n) + n := by
      rw [paper_alternant_pairIndex_card_eq_triangular]

/-- The paper's degree comparison reduces a divisible polynomial identity to
one scalar. The remaining normalization in Lemma 2.1 determines that scalar
from the lowest homogeneous part. -/
theorem paper_scalar_quotient_of_dvd_of_totalDegree_le
    {σ : Type*} (p q : MvPolynomial σ F)
    (hdiv : p ∣ q) (hp : p ≠ 0) (hq : q ≠ 0)
    (hdeg : q.totalDegree ≤ p.totalDegree) :
    ∃ c : F, q = p * MvPolynomial.C c := by
  rcases hdiv with ⟨r, hr⟩
  have hrne : r ≠ 0 := by
    intro hz
    rw [hr, hz] at hq
    simp at hq
  have hmuldeg : (p * r).totalDegree ≤ p.totalDegree := by
    simpa [hr] using hdeg
  rw [MvPolynomial.totalDegree_mul_of_isDomain hp hrne] at hmuldeg
  have hrdeg : r.totalDegree = 0 := by omega
  have hconstant : r = MvPolynomial.C (r.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hrdeg
  refine ⟨r.coeff 0, ?_⟩
  rw [hr, hconstant]
  simp

theorem paper_basic_factor_product_totalDegree_eq {n : ℕ} (t : F) (ht : t ≠ 0) :
    (paperBasicFactorProduct (n := n) t).totalDegree =
      3 * Fintype.card (paperAlternantPairIndex n) := by
  rw [paper_basic_factor_product_totalDegree t ht, paper_basic_factor_degree_sum,
    paper_alternant_pairIndex_card]

theorem paper_reciprocal_isRelPrime_difference {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
      MvPolynomial (Fin n) F) (MvPolynomial.X c - MvPolynomial.X d) := by
  rw [(paper_reciprocal_factor_irreducible t ht a b hab).isRelPrime_iff_not_dvd]
  intro hdiv
  have hne : (MvPolynomial.X c - MvPolynomial.X d : MvPolynomial (Fin n) F) ≠ 0 := by
    intro hz
    have hd := paper_difference_factor_totalDegree (F := F) c d hcd
    rw [hz] at hd
    simp at hd
  have hdegree := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hne
  rw [paper_reciprocal_factor_totalDegree t ht a b,
    paper_difference_factor_totalDegree c d hcd] at hdegree
  omega

theorem paper_ct_row_factor_totalDegree {n : ℕ} (t : F) (ht : t ≠ 0) (a : Fin n) :
    (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).totalDegree = 2 := by
  have htC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr ht
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.X_ne_zero a
  have hpow : (MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).totalDegree = 2 := by simp
  have hprod : (MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain htC (pow_ne_zero 2 hXa)]
    simp [hpow]
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) =
      -(MvPolynomial.C t * MvPolynomial.X a ^ 2) + 1 by ring,
    MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · simp [hprod]
  · simp [hprod]

theorem paper_ct_row_isRelPrime_reciprocal {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)
      (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) := by
  have hrec := paper_reciprocal_factor_irreducible t ht a b hab
  rw [isRelPrime_comm, hrec.isRelPrime_iff_not_dvd]
  intro hdiv
  let f : MvPolynomial (Fin n) F := 1 - MvPolynomial.C t * MvPolynomial.X a ^ 2
  let g : MvPolynomial (Fin n) F := 1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b
  have hgmul : g ∣ MvPolynomial.C t * MvPolynomial.X a *
      (MvPolynomial.X b - MvPolynomial.X a) := by
    have h := dvd_sub hdiv (dvd_rfl : g ∣ g)
    have heq : f - g = MvPolynomial.C t * MvPolynomial.X a *
        (MvPolynomial.X b - MvPolynomial.X a) := by
      dsimp [f, g]
      ring
    change g ∣ f - g at h
    rw [heq] at h
    exact h
  have hgprime : Prime g :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hrec
  rcases hgprime.dvd_mul.mp hgmul with hca | hdiff
  · rcases hgprime.dvd_mul.mp hca with htdiv | hadiv
    · have hne : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 :=
        MvPolynomial.C_ne_zero.mpr ht
      have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain htdiv hne
      rw [paper_reciprocal_factor_totalDegree t ht a b] at hd
      simp at hd
    · have hne : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 :=
        MvPolynomial.X_ne_zero a
      have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hadiv hne
      rw [paper_reciprocal_factor_totalDegree t ht a b] at hd
      simp at hd
  · have hne : (MvPolynomial.X b - MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      have hd := paper_difference_factor_totalDegree (F := F) b a hab.symm
      rw [hz] at hd
      simp at hd
    have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiff hne
    rw [paper_reciprocal_factor_totalDegree t ht a b,
      paper_difference_factor_totalDegree (F := F) b a hab.symm] at hd
    omega

theorem paper_difference_factor_degreeOf_left {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf a = 1 := by
  have hvars : (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).vars = {a, b} := by
    rw [MvPolynomial.vars_sub_of_disjoint (p := MvPolynomial.X a)
      (q := MvPolynomial.X b) (by simp [hab])]
    simp
  have ha : a ∈ (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).vars := by
    rw [hvars]
    simp
  have hne := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero (p :=
    MvPolynomial.X a - MvPolynomial.X b) (i := a)).mp ha
  have hle : (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf a ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ _
      _ = 1 := paper_difference_factor_totalDegree (F := F) a b hab
  omega

theorem paper_difference_factor_degreeOf_right {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf b = 1 := by
  have hvars : (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).vars = {a, b} := by
    rw [MvPolynomial.vars_sub_of_disjoint (p := MvPolynomial.X a)
      (q := MvPolynomial.X b) (by simp [hab])]
    simp
  have hb : b ∈ (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).vars := by
    rw [hvars]
    simp
  have hne := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero (p :=
    MvPolynomial.X a - MvPolynomial.X b) (i := b)).mp hb
  have hle : (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf b ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ _
      _ = 1 := paper_difference_factor_totalDegree (F := F) a b hab
  omega

theorem paper_difference_factor_degreeOf_outside {n : ℕ} (a b x : Fin n)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf x = 0 := by
  rw [sub_eq_add_neg]
  have hle := MvPolynomial.degreeOf_add_le x
    (MvPolynomial.X a : MvPolynomial (Fin n) F) (-MvPolynomial.X b)
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf x = 0 :=
    MvPolynomial.degreeOf_X_of_ne hxa
  have hXb : (-MvPolynomial.X b : MvPolynomial (Fin n) F).degreeOf x = 0 := by
    simpa using MvPolynomial.degreeOf_X_of_ne hxb
  omega

theorem paper_ct_row_factor_degreeOf_ne {n : ℕ} (t : F) (a x : Fin n) (hxa : x ≠ a) :
    (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).degreeOf x = 0 := by
  have hx : x ∉ (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 :
      MvPolynomial (Fin n) F).vars := by
    have hsub := MvPolynomial.vars_sub_subset
      (p := (1 : MvPolynomial (Fin n) F)) (q := MvPolynomial.C t * MvPolynomial.X a ^ 2)
    have hvars :
        (MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).vars ⊆ {a} := by
      calc
        _ ⊆ (MvPolynomial.C t).vars ∪ (MvPolynomial.X a ^ 2).vars :=
          MvPolynomial.vars_mul _ _
        _ ⊆ {a} := by
          simp only [MvPolynomial.vars_C, Finset.empty_union]
          exact (MvPolynomial.vars_pow _ 2).trans (by simp)
    have hrow := Finset.Subset.trans hsub (by simpa using hvars :
        (1 : MvPolynomial (Fin n) F).vars ∪
          (MvPolynomial.C t * MvPolynomial.X a ^ 2).vars ⊆ {a})
    exact fun hxmem => (hxa (by simpa using hrow hxmem))
  by_contra hne
  exact hx ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero (p :=
    (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)) (i := x)).mpr hne)

theorem paper_ct_row_isRelPrime_reciprocal_any {n : ℕ} (t : F) (ht : t ≠ 0)
    (a c d : Fin n) (hcd : c ≠ d) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)
      (1 - MvPolynomial.C t * MvPolynomial.X c * MvPolynomial.X d) := by
  have hrec := paper_reciprocal_factor_irreducible t ht c d hcd
  rw [isRelPrime_comm, hrec.isRelPrime_iff_not_dvd]
  by_cases hac : c = a
  · have hda : d ≠ a := by
      intro h
      exact hcd (hac.trans h.symm)
    apply paper_not_dvd_degreeOf_mismatch d
      (paper_reciprocal_factor_degreeOf_right t ht c d hcd)
      (paper_ct_row_factor_degreeOf_ne t a d hda)
      (by exact hrec.ne_zero)
      (by
        intro hz
        have hd := paper_ct_row_factor_totalDegree t ht a
        rw [hz] at hd
        simp at hd)
  · apply paper_not_dvd_degreeOf_mismatch c
      (paper_reciprocal_factor_degreeOf_left t ht c d hcd)
      (paper_ct_row_factor_degreeOf_ne t a c hac)
      (by exact hrec.ne_zero)
      (by
        intro hz
        have hd := paper_ct_row_factor_totalDegree t ht a
        rw [hz] at hd
        simp at hd)

theorem paper_ct_row_factor_degreeOf_self {n : ℕ} (t : F) (ht : t ≠ 0) (a : Fin n) :
    (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).degreeOf a = 2 := by
  have hC : (MvPolynomial.C t : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr ht
  have hX2 : (MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) ≠ 0 :=
    pow_ne_zero 2 (MvPolynomial.X_ne_zero a)
  have hprod : (MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F).degreeOf a = 2 := by
    rw [MvPolynomial.degreeOf_mul_eq hC hX2]
    simp
  have hneg : (-(MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)).degreeOf a = 2 := by
    simpa using hprod
  rw [show (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) =
      -(MvPolynomial.C t * MvPolynomial.X a ^ 2) + 1 by ring,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := a) (by simp [hneg])]
  exact hneg

theorem paper_ct_row_isRelPrime_difference {n : ℕ} (t : F) (ht : t ≠ 0) (a c d : Fin n)
    (hcd : c ≠ d) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)
      (MvPolynomial.X c - MvPolynomial.X d) := by
  have hirr := paper_difference_factor_irreducible (F := F) c d hcd
  rw [isRelPrime_comm, hirr.isRelPrime_iff_not_dvd]
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  by_cases hca : c = a
  · have hda : d ≠ a := by
      intro h
      exact hcd (hca.trans h.symm)
    have hdiffdegree := paper_difference_factor_degreeOf_right (F := F) c d hcd
    have hrowdegree := paper_ct_row_factor_degreeOf_ne (F := F) t a d hda
    have hdiffne : (MvPolynomial.X c - MvPolynomial.X d : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      rw [hz] at hdiffdegree
      simp at hdiffdegree
    have hrowne : (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      have htmp := paper_ct_row_factor_totalDegree t ht a
      rw [hz] at htmp
      simp at htmp
    have hqne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hq
      exact hrowne hq
    rw [hq, MvPolynomial.degreeOf_mul_eq hdiffne hqne] at hrowdegree
    omega
  · have hca' : c ≠ a := hca
    have hdiffdegree := paper_difference_factor_degreeOf_left (F := F) c d hcd
    have hrowdegree := paper_ct_row_factor_degreeOf_ne (F := F) t a c hca'
    have hdiffne : (MvPolynomial.X c - MvPolynomial.X d : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      rw [hz] at hdiffdegree
      simp at hdiffdegree
    have hrowne : (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      have htmp := paper_ct_row_factor_totalDegree t ht a
      rw [hz] at htmp
      simp at htmp
    have hqne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hq
      exact hrowne hq
    rw [hq, MvPolynomial.degreeOf_mul_eq hdiffne hqne] at hrowdegree
    omega

theorem paper_ct_row_isRelPrime_sum {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)
      (MvPolynomial.X a + MvPolynomial.X b) := by
  have hirr := paper_sum_factor_irreducible (F := F) a b hab
  rw [isRelPrime_comm, hirr.isRelPrime_iff_not_dvd]
  apply paper_not_dvd_degreeOf_mismatch b
    (paper_sum_factor_degreeOf_right (F := F) a b hab)
    (paper_ct_row_factor_degreeOf_ne (F := F) t a b hab.symm)
    (by exact hirr.ne_zero)
    (by
      intro hz
      have hd := paper_ct_row_factor_totalDegree t ht a
      rw [hz] at hd
      simp at hd)

theorem paper_ct_rows_isRelPrime {n : ℕ} (t : F) (ht : t ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    IsRelPrime (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F)
      (1 - MvPolynomial.C t * MvPolynomial.X b ^ 2) := by
  have hfa : (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) ≠ 0 := by
    intro hz
    have hd := paper_ct_row_factor_totalDegree t ht a
    rw [hz] at hd
    simp at hd
  rw [UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hfa]
  intro d hda hdb hdprime
  have hdiff : d ∣ (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) -
      (1 - MvPolynomial.C t * MvPolynomial.X b ^ 2) := dvd_sub hda hdb
  have hfactor :
      (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2 : MvPolynomial (Fin n) F) -
        (1 - MvPolynomial.C t * MvPolynomial.X b ^ 2) =
        MvPolynomial.C t * ((MvPolynomial.X b - MvPolynomial.X a) *
          (MvPolynomial.X a + MvPolynomial.X b)) := by ring
  rw [hfactor] at hdiff
  rcases hdprime.dvd_mul.mp hdiff with hCt | hprod
  · have hCunit : IsUnit (MvPolynomial.C t : MvPolynomial (Fin n) F) := by
      refine ⟨⟨MvPolynomial.C t, MvPolynomial.C t⁻¹, ?_, ?_⟩, rfl⟩
      · rw [← MvPolynomial.C_mul, mul_inv_cancel₀ ht, MvPolynomial.C_1]
      · rw [← MvPolynomial.C_mul, inv_mul_cancel₀ ht, MvPolynomial.C_1]
    exact hdprime.not_isUnit (isUnit_of_dvd_unit hCt hCunit)
  · rcases hdprime.dvd_mul.mp hprod with hdiff | hsum
    · have hcop := paper_ct_row_isRelPrime_difference t ht a b a hab.symm
      exact hdprime.not_isUnit (hcop hda hdiff)
    · have hcop := paper_ct_row_isRelPrime_sum t ht a b hab
      exact hdprime.not_isUnit (hcop hda (by simpa [add_comm] using hsum))

theorem paper_difference_isRelPrime_difference {n : ℕ}
    (a b c d : Fin n) (hab : a < b) (hcd : c < d)
    (hne : a ≠ c ∨ b ≠ d) :
    IsRelPrime (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) F)
      (MvPolynomial.X c - MvPolynomial.X d) := by
  have hirr := paper_difference_factor_irreducible (F := F) a b hab.ne
  rw [hirr.isRelPrime_iff_not_dvd]
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h
      exact hne.elim (fun hn => hn hac) (fun hn => hn h)
    apply paper_not_dvd_degreeOf_mismatch b
      (paper_difference_factor_degreeOf_right (F := F) a b hab.ne)
      (paper_difference_factor_degreeOf_outside (F := F) c d b
        (by simpa [hac] using hab.ne.symm) hbd)
      (by
        intro hz
        have hd := paper_difference_factor_totalDegree (F := F) a b hab.ne
        rw [hz] at hd
        simp at hd)
      (by
        intro hz
        have hd := paper_difference_factor_totalDegree (F := F) c d hcd.ne
        rw [hz] at hd
        simp at hd)
  · by_cases had : a = d
    · have hbc : b ≠ c := by
        intro h
        have : c < a := by simpa [had] using hcd
        omega
      have hbd : b ≠ d := by omega
      apply paper_not_dvd_degreeOf_mismatch b
        (paper_difference_factor_degreeOf_right (F := F) a b hab.ne)
        (paper_difference_factor_degreeOf_outside (F := F) c d b hbc hbd)
        (by
          intro hz
          have hd := paper_difference_factor_totalDegree (F := F) a b hab.ne
          rw [hz] at hd
          simp at hd)
        (by
          intro hz
          have hd := paper_difference_factor_totalDegree (F := F) c d hcd.ne
          rw [hz] at hd
          simp at hd)
    · apply paper_not_dvd_degreeOf_mismatch a
        (paper_difference_factor_degreeOf_left (F := F) a b hab.ne)
        (paper_difference_factor_degreeOf_outside (F := F) c d a hac had)
        (by
          intro hz
          have hd := paper_difference_factor_totalDegree (F := F) a b hab.ne
          rw [hz] at hd
          simp at hd)
        (by
          intro hz
          have hd := paper_difference_factor_totalDegree (F := F) c d hcd.ne
          rw [hz] at hd
          simp at hd)

theorem paper_basic_factor_pairwise_isRelPrime {n : ℕ} (t : F) (ht : t ≠ 0) :
    Pairwise (fun i j : paperBasicFactorIndex n =>
      IsRelPrime (paperBasicFactor t i) (paperBasicFactor t j)) := by
  classical
  intro i j hij
  rcases i with ⟨p, bi⟩
  rcases j with ⟨q, bj⟩
  cases bi <;> cases bj
  · have hpq : p ≠ q := by
      intro hpq
      apply hij
      cases hpq
      rfl
    have hcoords : p.1 ≠ q.1 ∨ p.2.1 ≠ q.2.1 := by
      by_contra hn
      push Not at hn
      apply hpq
      cases p with
      | mk a pa =>
        cases q with
        | mk c qc =>
          simp only [Sigma.mk.inj_iff] at hn ⊢
          rcases hn with ⟨hac, hval⟩
          cases hac
          exact ⟨rfl, heq_of_eq (Subtype.ext hval)⟩
    simpa [paperBasicFactor] using
      paper_difference_isRelPrime_difference p.1 p.2.1 q.1 q.2.1
        p.2.2 q.2.2 hcoords
  · simpa [paperBasicFactor] using
      (isRelPrime_comm.mp <| paper_reciprocal_isRelPrime_difference t ht q.1 q.2.1 p.1 p.2.1
        q.2.2.ne p.2.2.ne)
  · simpa [paperBasicFactor, isRelPrime_comm] using
      paper_reciprocal_isRelPrime_difference t ht p.1 p.2.1 q.1 q.2.1
        p.2.2.ne q.2.2.ne
  · have hpq : p ≠ q := by
      intro hpq
      apply hij
      cases hpq
      rfl
    have hcoords : p.1 ≠ q.1 ∨ p.2.1 ≠ q.2.1 := by
      by_contra hn
      push Not at hn
      apply hpq
      cases p with
      | mk a pa =>
        cases q with
        | mk c qc =>
          simp only [Sigma.mk.inj_iff] at hn ⊢
          rcases hn with ⟨hac, hval⟩
          cases hac
          exact ⟨rfl, heq_of_eq (Subtype.ext hval)⟩
    simpa [paperBasicFactor] using
      paper_reciprocal_isRelPrime_reciprocal t ht p.1 p.2.1 q.1 q.2.1
        p.2.2 q.2.2 hcoords

theorem paper_ct_factor_pairwise_isRelPrime {n : ℕ} (t : F) (ht : t ≠ 0) :
    Pairwise (fun i j : paperCtFactorIndex n =>
      IsRelPrime (paperCtFactor t i) (paperCtFactor t j)) := by
  classical
  intro i j hij
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          have hpq : p ≠ q := by
            intro hpq
            apply hij
            cases hpq
            rfl
          exact paper_basic_factor_pairwise_isRelPrime (n := n) t ht hpq
      | inr a =>
          cases hb : p.2
          · simpa [paperCtFactor, paperBasicFactor, hb] using
              (isRelPrime_comm.mp <| paper_ct_row_isRelPrime_difference t ht a
                p.1.1 p.1.2.1 (ne_of_lt p.1.2.2))
          · simpa [paperCtFactor, paperBasicFactor, hb] using
              (isRelPrime_comm.mp <| paper_ct_row_isRelPrime_reciprocal_any t ht a
                p.1.1 p.1.2.1 (ne_of_lt p.1.2.2))
  | inr a =>
      cases j with
      | inl q =>
          cases hb : q.2
          · simpa [paperCtFactor, paperBasicFactor, hb] using
              paper_ct_row_isRelPrime_difference t ht a q.1.1 q.1.2.1
                (ne_of_lt q.1.2.2)
          · simpa [paperCtFactor, paperBasicFactor, hb] using
              paper_ct_row_isRelPrime_reciprocal_any t ht a q.1.1 q.1.2.1
                (ne_of_lt q.1.2.2)
      | inr b =>
          have hab : a ≠ b := by
            intro h
            apply hij
            subst b
            rfl
          exact paper_ct_rows_isRelPrime t ht a b hab

theorem paper_bminus_row_factor_totalDegree {n : ℕ} (τ : F) (hτ : τ ≠ 0) (a : Fin n) :
    (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).totalDegree = 1 := by
  have hτC : (MvPolynomial.C τ : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hτ
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 :=
    MvPolynomial.X_ne_zero a
  have hprod : (MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hτC hXa]
    simp
  rw [show (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) =
      MvPolynomial.C τ * MvPolynomial.X a + 1 by ring,
    MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · simp [hprod]
  · simp [hprod]

theorem paper_bminus_row_factor_irreducible {n : ℕ} (τ : F) (hτ : τ ≠ 0) (a : Fin n) :
    Irreducible (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) := by
  have hC : (MvPolynomial.C τ : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr hτ
  have hXa : a ∉ (MvPolynomial.C τ : MvPolynomial (Fin n) F).vars := by simp
  have hig : a ∉ (1 : MvPolynomial (Fin n) F).vars := by simp
  have hirr := MvPolynomial.irreducible_mul_X_add
    (MvPolynomial.C τ) (1 : MvPolynomial (Fin n) F) a hC hXa hig isRelPrime_one_right
  rw [show (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) =
      MvPolynomial.C τ * MvPolynomial.X a + 1 by ring]
  exact hirr

theorem paper_bminus_row_factor_degreeOf_self {n : ℕ} (τ : F) (hτ : τ ≠ 0) (a : Fin n) :
    (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf a = 1 := by
  have hC : (MvPolynomial.C τ : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.C_ne_zero.mpr hτ
  have hXa : (MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := MvPolynomial.X_ne_zero a
  have hprod : (MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf a = 1 := by
    rw [MvPolynomial.degreeOf_mul_eq hC hXa]
    simp
  rw [show (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) =
      MvPolynomial.C τ * MvPolynomial.X a + 1 by ring,
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := a) (by simp [hprod])]
  exact hprod

theorem paper_bminus_row_factor_degreeOf_ne {n : ℕ} (τ : F) (a x : Fin n) (hxa : x ≠ a) :
    (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf x = 0 := by
  have hprod_le : (MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf x ≤ 0 := by
    have h := MvPolynomial.degreeOf_mul_le x (MvPolynomial.C τ) (MvPolynomial.X a)
    simpa [MvPolynomial.degreeOf_X_of_ne hxa] using h
  have hprod : (MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf x = 0 :=
    Nat.eq_zero_of_le_zero hprod_le
  have hle : (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F).degreeOf x ≤ 0 := by
    rw [show (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) =
        MvPolynomial.C τ * MvPolynomial.X a + 1 by ring]
    exact (MvPolynomial.degreeOf_add_le x _ _).trans (by simp [hprod])
  omega

theorem paper_bminus_row_isRelPrime_difference {n : ℕ} (τ : F) (a c d : Fin n)
    (hcd : c ≠ d) :
    IsRelPrime (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F)
      (MvPolynomial.X c - MvPolynomial.X d) := by
  have hirr := paper_difference_factor_irreducible (F := F) c d hcd
  rw [isRelPrime_comm, hirr.isRelPrime_iff_not_dvd]
  intro hdiv
  rcases hdiv with ⟨q, hq⟩
  by_cases hca : c = a
  · have hda : d ≠ a := by
      intro h
      exact hcd (hca.trans h.symm)
    have hdiffdegree := paper_difference_factor_degreeOf_right (F := F) c d hcd
    have hrowdegree := paper_bminus_row_factor_degreeOf_ne τ a d hda
    have hdiffne : (MvPolynomial.X c - MvPolynomial.X d : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      rw [hz] at hdiffdegree
      simp at hdiffdegree
    have hrowne : (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      have he := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : F))) hz
      simp at he
    have hqne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hq
      exact hrowne hq
    rw [hq, MvPolynomial.degreeOf_mul_eq hdiffne hqne] at hrowdegree
    omega
  · have hca' : c ≠ a := hca
    have hdiffdegree := paper_difference_factor_degreeOf_left (F := F) c d hcd
    have hrowdegree := paper_bminus_row_factor_degreeOf_ne τ a c hca'
    have hdiffne : (MvPolynomial.X c - MvPolynomial.X d : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      rw [hz] at hdiffdegree
      simp at hdiffdegree
    have hrowne : (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := by
      intro hz
      have he := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : F))) hz
      simp at he
    have hqne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hq
      exact hrowne hq
    rw [hq, MvPolynomial.degreeOf_mul_eq hdiffne hqne] at hrowdegree
    omega

theorem paper_bminus_row_isRelPrime_reciprocal {n : ℕ} (τ : F) (hτ : τ ≠ 0)
    (a c d : Fin n) (hcd : c ≠ d) :
    IsRelPrime (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F)
      (1 - MvPolynomial.C (τ ^ 2) * MvPolynomial.X c * MvPolynomial.X d) := by
  have hrec := paper_reciprocal_factor_irreducible (F := F) (τ ^ 2)
    (pow_ne_zero 2 hτ) c d hcd
  rw [isRelPrime_comm, hrec.isRelPrime_iff_not_dvd]
  intro hdiv
  have hrowne : (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F) ≠ 0 := by
    intro hz
    have he := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : F))) hz
    simp at he
  have hd := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hrowne
  rw [paper_reciprocal_factor_totalDegree (τ ^ 2) (pow_ne_zero 2 hτ) c d,
    paper_bminus_row_factor_totalDegree τ hτ a] at hd
  omega

theorem paper_bminus_rows_isRelPrime {n : ℕ} (τ : F) (hτ : τ ≠ 0)
    (a b : Fin n) (hab : a ≠ b) :
    IsRelPrime (1 + MvPolynomial.C τ * MvPolynomial.X a : MvPolynomial (Fin n) F)
      (1 + MvPolynomial.C τ * MvPolynomial.X b) := by
  have hirr := paper_bminus_row_factor_irreducible τ hτ a
  rw [hirr.isRelPrime_iff_not_dvd]
  apply paper_not_dvd_degreeOf_mismatch a
    (paper_bminus_row_factor_degreeOf_self τ hτ a)
    (paper_bminus_row_factor_degreeOf_ne τ b a hab)
    (by exact hirr.ne_zero)
    (by
      intro hz
      have he := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : F))) hz
      simp at he)

theorem paper_bminus_factor_pairwise_isRelPrime {n : ℕ} (τ : F) (hτ : τ ≠ 0) :
    Pairwise (fun i j : paperBminusFactorIndex n =>
      IsRelPrime (paperBminusFactor τ i) (paperBminusFactor τ j)) := by
  classical
  intro i j hij
  cases i with
  | inl p =>
      cases j with
      | inl q =>
          have hpq : p ≠ q := by
            intro hpq
            apply hij
            cases hpq
            rfl
          exact paper_basic_factor_pairwise_isRelPrime (n := n) (τ ^ 2)
            (pow_ne_zero 2 hτ) hpq
      | inr a =>
          cases hb : p.2
          · simpa [paperBminusFactor, paperBasicFactor, hb] using
              (isRelPrime_comm.mp <| paper_bminus_row_isRelPrime_difference τ
                a p.1.1 p.1.2.1 (ne_of_lt p.1.2.2))
          · simpa [paperBminusFactor, paperBasicFactor, hb] using
              (isRelPrime_comm.mp <| paper_bminus_row_isRelPrime_reciprocal τ hτ
                a p.1.1 p.1.2.1 (ne_of_lt p.1.2.2))
  | inr a =>
      cases j with
      | inl q =>
          cases hb : q.2
          · simpa [paperBminusFactor, paperBasicFactor, hb] using
              paper_bminus_row_isRelPrime_difference τ a q.1.1 q.1.2.1
                (ne_of_lt q.1.2.2)
          · simpa [paperBminusFactor, paperBasicFactor, hb] using
              paper_bminus_row_isRelPrime_reciprocal τ hτ a q.1.1 q.1.2.1
                (ne_of_lt q.1.2.2)
      | inr b =>
          have hab : a ≠ b := by
            intro h
            apply hij
            subst b
            rfl
          exact paper_bminus_rows_isRelPrime τ hτ a b hab

theorem paper_ct_factor_product_totalDegree {n : ℕ} (t : F) (ht : t ≠ 0) :
    (paperCtFactorProduct (n := n) t).totalDegree =
      ∑ i : paperCtFactorIndex n, (paperCtFactor t i).totalDegree := by
  classical
  change (∏ i : paperCtFactorIndex n, paperCtFactor t i).totalDegree = _
  apply paper_totalDegree_finsetProd_eq_sum
  intro i hi
  cases i with
  | inl p =>
      have hd := paper_basic_factor_totalDegree t ht p
      intro hz
      change paperBasicFactor t p = 0 at hz
      rw [hz] at hd
      cases hbool : p.2 <;> simp [hbool] at hd
  | inr a =>
      have hd := paper_ct_row_factor_totalDegree t ht a
      intro hz
      change (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2) = 0 at hz
      rw [hz] at hd
      simp at hd

theorem paper_bminus_factor_product_totalDegree {n : ℕ} (τ : F) (hτ : τ ≠ 0) :
    (paperBminusFactorProduct (n := n) τ).totalDegree =
      ∑ i : paperBminusFactorIndex n, (paperBminusFactor τ i).totalDegree := by
  classical
  change (∏ i : paperBminusFactorIndex n, paperBminusFactor τ i).totalDegree = _
  apply paper_totalDegree_finsetProd_eq_sum
  intro i hi
  cases i with
  | inl p =>
      have ht2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
      have hd := paper_basic_factor_totalDegree (τ ^ 2) ht2 p
      intro hz
      change paperBasicFactor (τ ^ 2) p = 0 at hz
      rw [hz] at hd
      cases hbool : p.2 <;> simp [hbool] at hd
  | inr a =>
      have hd := paper_bminus_row_factor_totalDegree τ hτ a
      intro hz
      change (1 + MvPolynomial.C τ * MvPolynomial.X a) = 0 at hz
      rw [hz] at hd
      simp at hd

theorem paper_ct_factor_product_totalDegree_eq {n : ℕ} (t : F) (ht : t ≠ 0) :
    (paperCtFactorProduct (n := n) t).totalDegree =
      3 * Fintype.card (paperAlternantPairIndex n) + 2 * n := by
  rw [paper_ct_factor_product_totalDegree t ht]
  simp only [paperCtFactorIndex, Fintype.sum_sum_type]
  have hbasic :
      (∑ p : paperBasicFactorIndex n, (paperCtFactor t (Sum.inl p)).totalDegree) =
        3 * Fintype.card (paperAlternantPairIndex n) := by
    calc
      _ = ∑ p : paperBasicFactorIndex n, if p.2 then 2 else 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            simpa [paperCtFactor] using paper_basic_factor_totalDegree t ht p
      _ = _ := paper_basic_factor_degree_sum
  have hrows :
      (∑ a : Fin n, (paperCtFactor t (Sum.inr a)).totalDegree) = 2 * n := by
    calc
      _ = ∑ _a : Fin n, 2 := by
            apply Finset.sum_congr rfl
            intro a ha
            simpa [paperCtFactor] using paper_ct_row_factor_totalDegree t ht a
      _ = _ := by simp; ring
  rw [hbasic]
  rw [hrows]

theorem paper_bminus_factor_product_totalDegree_eq {n : ℕ} (τ : F) (hτ : τ ≠ 0) :
    (paperBminusFactorProduct (n := n) τ).totalDegree =
      3 * Fintype.card (paperAlternantPairIndex n) + n := by
  rw [paper_bminus_factor_product_totalDegree τ hτ]
  simp only [paperBminusFactorIndex, Fintype.sum_sum_type]
  have ht2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
  have hbasic :
      (∑ p : paperBasicFactorIndex n,
        (paperBminusFactor τ (Sum.inl p)).totalDegree) =
        3 * Fintype.card (paperAlternantPairIndex n) := by
    calc
      _ = ∑ p : paperBasicFactorIndex n, if p.2 then 2 else 1 := by
            apply Finset.sum_congr rfl
            intro p hp
            simpa [paperBminusFactor] using paper_basic_factor_totalDegree (τ ^ 2) ht2 p
      _ = _ := paper_basic_factor_degree_sum
  have hrows :
      (∑ a : Fin n, (paperBminusFactor τ (Sum.inr a)).totalDegree) = n := by
    calc
      _ = ∑ _a : Fin n, 1 := by
            apply Finset.sum_congr rfl
            intro a ha
            simpa [paperBminusFactor] using paper_bminus_row_factor_totalDegree τ hτ a
      _ = _ := by simp
  rw [hbasic]
  rw [hrows]

theorem paper_basic_factor_product_eq_Nt {n : ℕ} (t : F) :
    paperBasicFactorProduct (n := n) t =
      Nt (R := MvPolynomial (Fin n) F) (n := n)
        (MvPolynomial.C t) (MvPolynomial.X (R := F) (σ := Fin n)) := by
  classical
  simp [paperBasicFactorProduct, paperBasicFactor, paperBasicFactorIndex,
    paperAlternantPairIndex, Nt, Fintype.prod_sigma, mul_comm]
  rfl

/-- For the basic alternant, the reciprocal substitution in its last variable
proves divisibility by the corresponding factor `1-t*z_a*z_b`. This is the
univariate root and Gauss-lemma step from the paper. -/
theorem paper_basic_last_variable_factor_dvd {n : ℕ} (t : F) (j : Fin n)
    (ht : t ≠ 0) :
    (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0 :
        MvPolynomial (Fin n.succ) F) ∣
      paperBasicAlternantPolynomial (F := F) (n := n.succ) t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.C t * MvPolynomial.X j
  let root : K := (φ c)⁻¹
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hc : c ≠ 0 := mul_ne_zero (MvPolynomial.C_ne_zero.mpr ht) (MvPolynomial.X_ne_zero _)
  have hφc : φ c ≠ 0 := by
    intro h
    dsimp [φ] at h
    exact hc ((IsFractionRing.injective R K) (by simpa using h))
  have hroot : z 0 = (f t * z j.succ)⁻¹ := by
    change root = (f t * φ (MvPolynomial.X j))⁻¹
    simp [root, f, c, φ]
  have hzj : z j.succ ≠ 0 := by
    change φ (MvPolynomial.X j) ≠ 0
    intro h
    dsimp [φ] at h
    exact MvPolynomial.X_ne_zero j ((IsFractionRing.injective R K) (by simpa using h))
  have hvan := paper_basic_alternant_vanish_under_reciprocal
    (F := K) (n := n.succ) (t := f t) (z := z) (a := j.succ) (b := 0) (by simp) (by
      intro h
      exact ht ((RingHom.injective f) (by simpa only [map_zero] using h)))
    hzj hroot
  have heval : MvPolynomial.eval₂Hom f z
      (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_fColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperBasicAlternantPolynomial (F := F) (n := n.succ) t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperBasicAlternantPolynomial (F := F) (n := n.succ) t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hfactor_map :
      (1 - Polynomial.C c * Polynomial.X).map φ =
        (Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c) := by
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rw [sub_mul, ← Polynomial.C_mul]
    have hr : root * (-φ c) = -1 := by
      calc
        root * (-φ c) = -(root * φ c) := by ring
        _ = -1 := by dsimp [root]; rw [inv_mul_cancel₀ hφc]
    rw [hr]
    have hneg : Polynomial.C (-φ c) = -Polynomial.C (φ c) := map_neg _ _
    have hone : Polynomial.C (-1 : K) = -1 := map_neg _ _
    rw [hneg, hone]
    ring
  obtain ⟨q, hq⟩ := hroot_dvd
  have hmap_dvd :
      ((1 - Polynomial.C c * Polynomial.X).map φ) ∣ p.map φ := by
    refine ⟨Polynomial.C ((-φ c)⁻¹) * q, ?_⟩
    rw [hfactor_map, hq]
    have hscalar : (-φ c) * (-φ c)⁻¹ = 1 := mul_inv_cancel₀ (neg_ne_zero.mpr hφc)
    have hC : Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹) = 1 := by
      rw [← Polynomial.C_mul, hscalar, Polynomial.C_1]
    calc
      (Polynomial.X - Polynomial.C root) * q =
          (Polynomial.X - Polynomial.C root) *
            (Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹)) * q := by rw [hC]; simp
      _ = ((Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c)) *
            (Polynomial.C ((-φ c)⁻¹) * q) := by ring
  have hprimitive : (1 - Polynomial.C c * Polynomial.X).IsPrimitive := by
    intro r hr
    have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
      (1 - Polynomial.C c * Polynomial.X)).1 hr 0
    have hzero : (1 - Polynomial.C c * Polynomial.X).coeff 0 = 1 := by simp
    rw [hzero] at hcoeff
    exact isUnit_of_dvd_one hcoeff
  have hpoly_dvd : (1 - Polynomial.C c * Polynomial.X) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C t) = Polynomial.C (MvPolynomial.C t) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hfactor : E (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) =
      1 - Polynomial.C c * Polynomial.X := by
    simp [E, c, hct, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  apply E.injective
  change E (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) =
    E ((1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (1 - Polynomial.C c * Polynomial.X) * q
  exact hq

def paperCtAlternantPolynomial {n : ℕ} (t : F) :
    MvPolynomial (Fin n) F :=
  (Matrix.of fun a r : Fin n =>
    ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n) F)).det

theorem paper_ct_last_variable_factor_dvd {n : ℕ} (t : F) (j : Fin n)
    (ht : t ≠ 0) :
    (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0 :
        MvPolynomial (Fin n.succ) F) ∣
      paperCtAlternantPolynomial (F := F) (n := n.succ) t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.C t * MvPolynomial.X j
  let root : K := (φ c)⁻¹
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hc : c ≠ 0 := mul_ne_zero
    (MvPolynomial.C_ne_zero.mpr ht) (MvPolynomial.X_ne_zero _)
  have hφc : φ c ≠ 0 := by
    intro h
    dsimp [φ] at h
    exact hc ((IsFractionRing.injective R K) (by simpa using h))
  have hroot : z 0 = (f t * z j.succ)⁻¹ := by
    change root = (f t * φ (MvPolynomial.X j))⁻¹
    simp [root, f, c, φ]
  have hzj : z j.succ ≠ 0 := by
    change φ (MvPolynomial.X j) ≠ 0
    intro h
    dsimp [φ] at h
    exact MvPolynomial.X_ne_zero j ((IsFractionRing.injective R K) (by simpa using h))
  have hvan := paper_ct_alternant_vanish_under_reciprocal
    (F := K) (n := n.succ) (t := f t) (z := z) (a := j.succ) (b := 0) (by simp) (by
      intro h
      exact ht ((RingHom.injective f) (by simpa only [map_zero] using h)))
    hzj (by omega) hroot
  have heval : MvPolynomial.eval₂Hom f z
      (paperCtAlternantPolynomial (F := F) (n := n.succ) t) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_ctAlternantColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperCtAlternantPolynomial (F := F) (n := n.succ) t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperCtAlternantPolynomial (F := F) (n := n.succ) t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hfactor_map :
      (1 - Polynomial.C c * Polynomial.X).map φ =
        (Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c) := by
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rw [sub_mul, ← Polynomial.C_mul]
    have hr : root * (-φ c) = -1 := by
      calc
        root * (-φ c) = -(root * φ c) := by ring
        _ = -1 := by dsimp [root]; rw [inv_mul_cancel₀ hφc]
    rw [hr]
    have hneg : Polynomial.C (-φ c) = -Polynomial.C (φ c) := map_neg _ _
    have hone : Polynomial.C (-1 : K) = -1 := map_neg _ _
    rw [hneg, hone]
    ring
  obtain ⟨q, hq⟩ := hroot_dvd
  have hmap_dvd :
      ((1 - Polynomial.C c * Polynomial.X).map φ) ∣ p.map φ := by
    refine ⟨Polynomial.C ((-φ c)⁻¹) * q, ?_⟩
    rw [hfactor_map, hq]
    have hscalar : (-φ c) * (-φ c)⁻¹ = 1 := mul_inv_cancel₀ (neg_ne_zero.mpr hφc)
    have hC : Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹) = 1 := by
      rw [← Polynomial.C_mul, hscalar, Polynomial.C_1]
    calc
      (Polynomial.X - Polynomial.C root) * q =
          (Polynomial.X - Polynomial.C root) *
            (Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹)) * q := by rw [hC]; simp
      _ = ((Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c)) *
            (Polynomial.C ((-φ c)⁻¹) * q) := by ring
  have hprimitive : (1 - Polynomial.C c * Polynomial.X).IsPrimitive := by
    intro r hr
    have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
      (1 - Polynomial.C c * Polynomial.X)).1 hr 0
    have hzero : (1 - Polynomial.C c * Polynomial.X).coeff 0 = 1 := by simp
    rw [hzero] at hcoeff
    exact isUnit_of_dvd_one hcoeff
  have hpoly_dvd : (1 - Polynomial.C c * Polynomial.X) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C t) = Polynomial.C (MvPolynomial.C t) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hfactor : E (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) =
      1 - Polynomial.C c * Polynomial.X := by
    simp [E, c, hct, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  apply E.injective
  change E (paperCtAlternantPolynomial (F := F) (n := n.succ) t) =
    E ((1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (1 - Polynomial.C c * Polynomial.X) * q
  exact hq

def paperBminusAlternantPolynomial {n : ℕ} (τ : F) :
    MvPolynomial (Fin n) F :=
  (Matrix.of fun a r : Fin n =>
    bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X a : MvPolynomial (Fin n) F)).det

theorem paper_bminus_last_variable_factor_dvd {n : ℕ} (τ : F) (j : Fin n)
    (hτ : τ ≠ 0) :
    (1 - MvPolynomial.C (τ^2) * MvPolynomial.X j.succ * MvPolynomial.X 0 :
        MvPolynomial (Fin n.succ) F) ∣
      paperBminusAlternantPolynomial (F := F) (n := n.succ) τ := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.C (τ^2) * MvPolynomial.X j
  let root : K := (φ c)⁻¹
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hc : c ≠ 0 := mul_ne_zero
    (MvPolynomial.C_ne_zero.mpr (pow_ne_zero 2 hτ)) (MvPolynomial.X_ne_zero _)
  have hφc : φ c ≠ 0 := by
    intro h
    dsimp [φ] at h
    exact hc ((IsFractionRing.injective R K) (by simpa using h))
  have hroot : z 0 = (f (τ^2) * z j.succ)⁻¹ := by
    change root = (f (τ^2) * φ (MvPolynomial.X j))⁻¹
    simp [root, f, c, φ]
  have hzj : z j.succ ≠ 0 := by
    change φ (MvPolynomial.X j) ≠ 0
    intro h
    dsimp [φ] at h
    exact MvPolynomial.X_ne_zero j ((IsFractionRing.injective R K) (by simpa using h))
  have hrootB : z 0 = ((f τ)^2 * z j.succ)⁻¹ := by
    simpa [map_pow] using hroot
  have hvan := paper_bminus_alternant_vanish_under_reciprocal
    (F := K) (n := n.succ) (τ := f τ) (z := z) (a := j.succ) (b := 0) (by simp) (by
      intro h
      exact hτ ((RingHom.injective f) (by simpa only [map_zero] using h)))
    hzj (by omega) hrootB
  have heval : MvPolynomial.eval₂Hom f z
      (paperBminusAlternantPolynomial (F := F) (n := n.succ) τ) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_bminusAlternantColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperBminusAlternantPolynomial (F := F) (n := n.succ) τ)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperBminusAlternantPolynomial (F := F) (n := n.succ) τ)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hfactor_map :
      (1 - Polynomial.C c * Polynomial.X).map φ =
        (Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c) := by
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rw [sub_mul, ← Polynomial.C_mul]
    have hr : root * (-φ c) = -1 := by
      calc
        root * (-φ c) = -(root * φ c) := by ring
        _ = -1 := by dsimp [root]; rw [inv_mul_cancel₀ hφc]
    rw [hr]
    have hneg : Polynomial.C (-φ c) = -Polynomial.C (φ c) := map_neg _ _
    have hone : Polynomial.C (-1 : K) = -1 := map_neg _ _
    rw [hneg, hone]
    ring
  obtain ⟨q, hq⟩ := hroot_dvd
  have hmap_dvd :
      ((1 - Polynomial.C c * Polynomial.X).map φ) ∣ p.map φ := by
    refine ⟨Polynomial.C ((-φ c)⁻¹) * q, ?_⟩
    rw [hfactor_map, hq]
    have hscalar : (-φ c) * (-φ c)⁻¹ = 1 := mul_inv_cancel₀ (neg_ne_zero.mpr hφc)
    have hC : Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹) = 1 := by
      rw [← Polynomial.C_mul, hscalar, Polynomial.C_1]
    calc
      (Polynomial.X - Polynomial.C root) * q =
          (Polynomial.X - Polynomial.C root) *
            (Polynomial.C (-φ c) * Polynomial.C ((-φ c)⁻¹)) * q := by rw [hC]; simp
      _ = ((Polynomial.X - Polynomial.C root) * Polynomial.C (-φ c)) *
            (Polynomial.C ((-φ c)⁻¹) * q) := by ring
  have hprimitive : (1 - Polynomial.C c * Polynomial.X).IsPrimitive := by
    intro r hr
    have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
      (1 - Polynomial.C c * Polynomial.X)).1 hr 0
    have hzero : (1 - Polynomial.C c * Polynomial.X).coeff 0 = 1 := by simp
    rw [hzero] at hcoeff
    exact isUnit_of_dvd_one hcoeff
  have hpoly_dvd : (1 - Polynomial.C c * Polynomial.X) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C τ) = Polynomial.C (MvPolynomial.C τ) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hfactor : E (1 - MvPolynomial.C (τ^2) * MvPolynomial.X j.succ * MvPolynomial.X 0) =
      1 - Polynomial.C c * Polynomial.X := by
    simp [E, c, hct, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  apply E.injective
  change E (paperBminusAlternantPolynomial (F := F) (n := n.succ) τ) =
    E ((1 - MvPolynomial.C (τ^2) * MvPolynomial.X j.succ * MvPolynomial.X 0) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (1 - Polynomial.C c * Polynomial.X) * q
  exact hq

theorem paper_basic_last_variable_difference_dvd {n : ℕ} (t : F) (j : Fin n) :
    (MvPolynomial.X 0 - MvPolynomial.X j.succ : MvPolynomial (Fin n.succ) F) ∣
      paperBasicAlternantPolynomial (F := F) (n := n.succ) t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.X j
  let root : K := φ c
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hzEq : z j.succ = z 0 := by simp [z, root, c]
  let M : Matrix (Fin n.succ) (Fin n.succ) K := fun a r => fColumn (f t) r (z a)
  have hrows : M j.succ = M 0 := by
    funext r
    simp [M, hzEq]
  have hvan : (Matrix.of fun a r : Fin n.succ => fColumn (f t) r (z a)).det = 0 := by
    exact Matrix.det_zero_of_row_eq (by simp) hrows
  have heval : MvPolynomial.eval₂Hom f z
      (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        fColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_fColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperBasicAlternantPolynomial (F := F) (n := n.succ) t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperBasicAlternantPolynomial (F := F) (n := n.succ) t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hprimitive : (Polynomial.X - Polynomial.C c).IsPrimitive :=
    (Polynomial.monic_X_sub_C c).isPrimitive
  have hmap_dvd : (Polynomial.X - Polynomial.C c).map φ ∣ p.map φ := by
    have hm : (Polynomial.X - Polynomial.C c).map φ = Polynomial.X - Polynomial.C root := by
      simp [root, c]
    simpa [hm] using hroot_dvd
  have hpoly_dvd : (Polynomial.X - Polynomial.C c) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C t) = Polynomial.C (MvPolynomial.C t) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hc : E (MvPolynomial.X j.succ) = Polynomial.C c := by
    simp [E, c, MvPolynomial.finSuccEquiv_X_succ]
  have hfactor : E (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
      Polynomial.X - Polynomial.C c := by
    simp [E, hc, MvPolynomial.finSuccEquiv_X_zero]
  apply E.injective
  change E (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) =
    E ((MvPolynomial.X 0 - MvPolynomial.X j.succ) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (Polynomial.X - Polynomial.C c) * q
  exact hq

theorem paper_ct_last_variable_difference_dvd {n : ℕ} (t : F) (j : Fin n) :
    (MvPolynomial.X 0 - MvPolynomial.X j.succ : MvPolynomial (Fin n.succ) F) ∣
      paperCtAlternantPolynomial (F := F) (n := n.succ) t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.X j
  let root : K := φ c
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hzEq : z j.succ = z 0 := by simp [z, root, c]
  let M : Matrix (Fin n.succ) (Fin n.succ) K := fun a r => ctAlternantColumn (f t) r (z a)
  have hrows : M j.succ = M 0 := by
    funext r
    simp [M, hzEq]
  have hvan : (Matrix.of fun a r : Fin n.succ => ctAlternantColumn (f t) r (z a)).det = 0 := by
    exact Matrix.det_zero_of_row_eq (by simp) hrows
  have heval : MvPolynomial.eval₂Hom f z
      (paperCtAlternantPolynomial (F := F) (n := n.succ) t) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_ctAlternantColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperCtAlternantPolynomial (F := F) (n := n.succ) t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperCtAlternantPolynomial (F := F) (n := n.succ) t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hprimitive : (Polynomial.X - Polynomial.C c).IsPrimitive :=
    (Polynomial.monic_X_sub_C c).isPrimitive
  have hmap_dvd : (Polynomial.X - Polynomial.C c).map φ ∣ p.map φ := by
    have hm : (Polynomial.X - Polynomial.C c).map φ = Polynomial.X - Polynomial.C root := by
      simp [root, c]
    simpa [hm] using hroot_dvd
  have hpoly_dvd : (Polynomial.X - Polynomial.C c) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C t) = Polynomial.C (MvPolynomial.C t) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hc : E (MvPolynomial.X j.succ) = Polynomial.C c := by
    simp [E, c, MvPolynomial.finSuccEquiv_X_succ]
  have hfactor : E (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
      Polynomial.X - Polynomial.C c := by
    simp [E, hc, MvPolynomial.finSuccEquiv_X_zero]
  apply E.injective
  change E (paperCtAlternantPolynomial (F := F) (n := n.succ) t) =
    E ((MvPolynomial.X 0 - MvPolynomial.X j.succ) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (Polynomial.X - Polynomial.C c) * q
  exact hq

/-- Transport the preceding one-variable Gauss argument to any ordered pair
of distinct variables. The permutation of variables changes the alternant
only by its determinant sign, a unit, so the same factor divides it. -/
theorem paper_bminus_last_variable_difference_dvd {n : ℕ} (t : F) (j : Fin n) :
    (MvPolynomial.X 0 - MvPolynomial.X j.succ : MvPolynomial (Fin n.succ) F) ∣
      paperBminusAlternantPolynomial (F := F) (n := n.succ) t := by
  classical
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let c : R := MvPolynomial.X j
  let root : K := φ c
  let f : F →+* K := φ.comp MvPolynomial.C
  let z : Fin n.succ → K := Fin.cases root (fun i => φ (MvPolynomial.X i))
  have hzEq : z j.succ = z 0 := by simp [z, root, c]
  let M : Matrix (Fin n.succ) (Fin n.succ) K := fun a r => bminusAlternantColumn (f t) r (z a)
  have hrows : M j.succ = M 0 := by
    funext r
    simp [M, hzEq]
  have hvan : (Matrix.of fun a r : Fin n.succ => bminusAlternantColumn (f t) r (z a)).det = 0 := by
    exact Matrix.det_zero_of_row_eq (by simp) hrows
  have heval : MvPolynomial.eval₂Hom f z
      (paperBminusAlternantPolynomial (F := F) (n := n.succ) t) = 0 := by
    change (MvPolynomial.eval₂Hom f z)
      ((Matrix.of fun a r : Fin n.succ =>
        bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X a : MvPolynomial (Fin n.succ) F)).det) = 0
    rw [RingHom.map_det]
    simpa [Matrix.map, map_bminusAlternantColumn, f] using hvan
  let p : Polynomial R := MvPolynomial.finSuccEquiv F n
    (paperBminusAlternantPolynomial (F := F) (n := n.succ) t)
  let ψ : Polynomial R →+* K := Polynomial.eval₂RingHom φ root
  have hψ : (ψ.comp (MvPolynomial.finSuccEquiv F n).toRingHom) =
      MvPolynomial.eval₂Hom f z := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, f, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [ψ, z, root, MvPolynomial.finSuccEquiv_X_zero]
      · intro i
        simp [ψ, z, φ, MvPolynomial.finSuccEquiv_X_succ]
  have hroot_eval : ψ p = 0 := by
    have h := congrArg (fun g : MvPolynomial (Fin n.succ) F →+* K =>
      g (paperBminusAlternantPolynomial (F := F) (n := n.succ) t)) hψ
    simpa [p] using h.trans heval
  have hmaproot : (p.map φ).eval root = 0 := by
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hroot_eval
  have hroot_dvd : (Polynomial.X - Polynomial.C root) ∣ p.map φ :=
    (Polynomial.dvd_iff_isRoot).2 hmaproot
  have hprimitive : (Polynomial.X - Polynomial.C c).IsPrimitive :=
    (Polynomial.monic_X_sub_C c).isPrimitive
  have hmap_dvd : (Polynomial.X - Polynomial.C c).map φ ∣ p.map φ := by
    have hm : (Polynomial.X - Polynomial.C c).map φ = Polynomial.X - Polynomial.C root := by
      simp [root, c]
    simpa [hm] using hroot_dvd
  have hpoly_dvd : (Polynomial.X - Polynomial.C c) ∣ p :=
    hprimitive.dvd_of_fraction_map_dvd_fraction_map hmap_dvd
  obtain ⟨q, hq⟩ := hpoly_dvd
  refine ⟨(MvPolynomial.finSuccEquiv F n).symm q, ?_⟩
  let E := MvPolynomial.finSuccEquiv F n
  have hct : E (MvPolynomial.C t) = Polynomial.C (MvPolynomial.C t) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  have hc : E (MvPolynomial.X j.succ) = Polynomial.C c := by
    simp [E, c, MvPolynomial.finSuccEquiv_X_succ]
  have hfactor : E (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
      Polynomial.X - Polynomial.C c := by
    simp [E, hc, MvPolynomial.finSuccEquiv_X_zero]
  apply E.injective
  change E (paperBminusAlternantPolynomial (F := F) (n := n.succ) t) =
    E ((MvPolynomial.X 0 - MvPolynomial.X j.succ) * E.symm q)
  rw [map_mul, hfactor, E.apply_symm_apply]
  change p = (Polynomial.X - Polynomial.C c) * q
  exact hq

/-- Transport the preceding one-variable Gauss argument to any ordered pair
of distinct variables. The permutation of variables changes the alternant
only by its determinant sign, a unit, so the same factor divides it. -/
theorem paper_basic_factor_dvd_any_pair {N : ℕ} (t : F)
    (a b : Fin N) (hab : a ≠ b) (ht : t ≠ 0) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
        MvPolynomial (Fin N) F) ∣ paperBasicAlternantPolynomial t := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by
      rw [hjs, e.apply_symm_apply]
    have hbase := paper_basic_last_variable_factor_dvd (F := F) (n := n) t j ht
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ
        (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) =
        1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b := by
      change MvPolynomial.rename e
        (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) =
        MvPolynomial.C s * paperBasicAlternantPolynomial (F := F) (n := n.succ) t := by
      rw [show paperBasicAlternantPolynomial (F := F) (n := n.succ) t =
        (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e
            (fColumn (MvPolynomial.C t) r (MvPolynomial.X i)) =
              fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i))
          simpa using map_fColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C t) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨MvPolynomial.C (s⁻¹) * q, ?_⟩
    calc
      paperBasicAlternantPolynomial (F := F) (n := n.succ) t =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperBasicAlternantPolynomial t) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) *
          ((1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) * q) := by
        rw [← hq]
      _ = (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) *
          (MvPolynomial.C (s⁻¹) * q) := by ring

theorem paper_ct_factor_dvd_any_pair {N : ℕ} (t : F)
    (a b : Fin N) (hab : a ≠ b) (ht : t ≠ 0) :
    (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b :
        MvPolynomial (Fin N) F) ∣ paperCtAlternantPolynomial t := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by
      rw [hjs, e.apply_symm_apply]
    have hbase := paper_ct_last_variable_factor_dvd (F := F) (n := n) t j ht
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ
        (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) =
        1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b := by
      change MvPolynomial.rename e
        (1 - MvPolynomial.C t * MvPolynomial.X j.succ * MvPolynomial.X 0) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperCtAlternantPolynomial (F := F) (n := n.succ) t) =
        MvPolynomial.C s * paperCtAlternantPolynomial (F := F) (n := n.succ) t := by
      rw [show paperCtAlternantPolynomial (F := F) (n := n.succ) t =
        (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e
            (ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i)) =
              ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i))
          simpa using map_ctAlternantColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C t) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨MvPolynomial.C (s⁻¹) * q, ?_⟩
    calc
      paperCtAlternantPolynomial (F := F) (n := n.succ) t =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperCtAlternantPolynomial t) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) *
          ((1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) * q) := by
        rw [← hq]
      _ = (1 - MvPolynomial.C t * MvPolynomial.X a * MvPolynomial.X b) *
          (MvPolynomial.C (s⁻¹) * q) := by ring

/-- The alternating row property similarly supplies `z_a-z_b` for every pair.
The normalized row permutation transports the canonical equality of two rows,
and its sign is a unit. -/
theorem paper_bminus_factor_dvd_any_pair {N : ℕ} (τ : F)
    (a b : Fin N) (hab : a ≠ b) (hτ : τ ≠ 0) :
    (1 - MvPolynomial.C (τ^2) * MvPolynomial.X a * MvPolynomial.X b :
        MvPolynomial (Fin N) F) ∣ paperBminusAlternantPolynomial τ := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by
      rw [hjs, e.apply_symm_apply]
    have hbase := paper_bminus_last_variable_factor_dvd (F := F) (n := n) τ j hτ
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ
        (1 - MvPolynomial.C (τ^2) * MvPolynomial.X j.succ * MvPolynomial.X 0) =
        1 - MvPolynomial.C (τ^2) * MvPolynomial.X a * MvPolynomial.X b := by
      change MvPolynomial.rename e
        (1 - MvPolynomial.C (τ^2) * MvPolynomial.X j.succ * MvPolynomial.X 0) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperBminusAlternantPolynomial (F := F) (n := n.succ) τ) =
        MvPolynomial.C s * paperBminusAlternantPolynomial (F := F) (n := n.succ) τ := by
      rw [show paperBminusAlternantPolynomial (F := F) (n := n.succ) τ =
        (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e
            (bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X i)) =
              bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X (e i))
          simpa using map_bminusAlternantColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C τ) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C τ) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨MvPolynomial.C (s⁻¹) * q, ?_⟩
    calc
      paperBminusAlternantPolynomial (F := F) (n := n.succ) τ =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperBminusAlternantPolynomial τ) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) *
          ((1 - MvPolynomial.C (τ^2) * MvPolynomial.X a * MvPolynomial.X b) * q) := by
        rw [← hq]
      _ = (1 - MvPolynomial.C (τ^2) * MvPolynomial.X a * MvPolynomial.X b) *
          (MvPolynomial.C (s⁻¹) * q) := by ring

/-- The alternating row property similarly supplies `z_a-z_b` for every pair.
The normalized row permutation transports the canonical equality of two rows,
and its sign is a unit. -/
theorem paper_basic_difference_factor_dvd_any_pair {N : ℕ} (t : F)
    (a b : Fin N) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin N) F) ∣
      paperBasicAlternantPolynomial t := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by rw [hjs, e.apply_symm_apply]
    have hbase := paper_basic_last_variable_difference_dvd (F := F) (n := n) t j
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
        MvPolynomial.X b - MvPolynomial.X a := by
      change MvPolynomial.rename e (MvPolynomial.X 0 - MvPolynomial.X j.succ) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperBasicAlternantPolynomial (F := F) (n := n.succ) t) =
        MvPolynomial.C s * paperBasicAlternantPolynomial (F := F) (n := n.succ) t := by
      rw [show paperBasicAlternantPolynomial (F := F) (n := n.succ) t =
        (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e (fColumn (MvPolynomial.C t) r (MvPolynomial.X i)) =
            fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i))
          simpa using map_fColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C t) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          fColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨-(MvPolynomial.C (s⁻¹) * q), ?_⟩
    calc
      paperBasicAlternantPolynomial (F := F) (n := n.succ) t =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperBasicAlternantPolynomial t) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) * ((MvPolynomial.X b - MvPolynomial.X a) * q) := by
        rw [← hq]
      _ = (MvPolynomial.X a - MvPolynomial.X b) *
          (-(MvPolynomial.C (s⁻¹) * q)) := by ring

/- The paper's pairwise-coprimality claim for the reciprocal and difference
factors is proved by irreducibility and degree-in-a-variable comparisons. -/
theorem paper_basic_full_factor_product_dvd {n : ℕ} (t : F) (ht : t ≠ 0) :
    paperBasicFactorProduct (n := n) t ∣ paperBasicAlternantPolynomial t := by
  classical
  have hcop := paper_basic_factor_pairwise_isRelPrime (n := n) t ht
  apply Fintype.prod_dvd_of_isRelPrime hcop
  intro i
  by_cases hi : i.2
  · simp only [paperBasicFactor, hi]
    exact paper_basic_factor_dvd_any_pair t i.1.1 i.1.2.1
      (ne_of_lt i.1.2.2) ht
  · simp only [paperBasicFactor, hi]
    exact paper_basic_difference_factor_dvd_any_pair t i.1.1 i.1.2.1
      (ne_of_lt i.1.2.2)

theorem paper_ct_factor_product_eq {n : ℕ} (t : F) :
    paperCtFactorProduct (n := n) t =
      (∏ a : Fin n, (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2)) *
        Nt (R := MvPolynomial (Fin n) F) (n := n)
          (MvPolynomial.C t) (MvPolynomial.X (R := F) (σ := Fin n)) := by
  classical
  have hprod : paperCtFactorProduct t =
      (∏ i : paperBasicFactorIndex n, paperBasicFactor t i) *
        (∏ a : Fin n, (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2)) := by
    simp [paperCtFactorProduct, paperCtFactor, paperCtFactorIndex, Fintype.prod_sum_type]
  rw [hprod]
  change paperBasicFactorProduct t *
      (∏ a : Fin n, (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2)) = _
  rw [paper_basic_factor_product_eq_Nt, mul_comm]

theorem paper_bminus_factor_product_eq {n : ℕ} (τ : F) :
    paperBminusFactorProduct (n := n) τ =
      (∏ a : Fin n, (1 + MvPolynomial.C τ * MvPolynomial.X a)) *
        Nt (R := MvPolynomial (Fin n) F) (n := n)
          (MvPolynomial.C (τ^2)) (MvPolynomial.X (R := F) (σ := Fin n)) := by
  classical
  have hprod : paperBminusFactorProduct τ =
      (∏ i : paperBasicFactorIndex n, paperBasicFactor (τ^2) i) *
        (∏ a : Fin n, (1 + MvPolynomial.C τ * MvPolynomial.X a)) := by
    simp [paperBminusFactorProduct, paperBminusFactor, paperBminusFactorIndex,
      Fintype.prod_sum_type]
  rw [hprod]
  change paperBasicFactorProduct (τ^2) *
      (∏ a : Fin n, (1 + MvPolynomial.C τ * MvPolynomial.X a)) = _
  rw [paper_basic_factor_product_eq_Nt, mul_comm]

theorem paper_ct_difference_factor_dvd_any_pair {N : ℕ} (t : F)
    (a b : Fin N) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin N) F) ∣
      paperCtAlternantPolynomial t := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by rw [hjs, e.apply_symm_apply]
    have hbase := paper_ct_last_variable_difference_dvd (F := F) (n := n) t j
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
        MvPolynomial.X b - MvPolynomial.X a := by
      change MvPolynomial.rename e (MvPolynomial.X 0 - MvPolynomial.X j.succ) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperCtAlternantPolynomial (F := F) (n := n.succ) t) =
        MvPolynomial.C s * paperCtAlternantPolynomial (F := F) (n := n.succ) t := by
      rw [show paperCtAlternantPolynomial (F := F) (n := n.succ) t =
        (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e (ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i)) =
            ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i))
          simpa using map_ctAlternantColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C t) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          ctAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨-(MvPolynomial.C (s⁻¹) * q), ?_⟩
    calc
      paperCtAlternantPolynomial (F := F) (n := n.succ) t =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperCtAlternantPolynomial t) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) * ((MvPolynomial.X b - MvPolynomial.X a) * q) := by
        rw [← hq]
      _ = (MvPolynomial.X a - MvPolynomial.X b) *
          (-(MvPolynomial.C (s⁻¹) * q)) := by ring

/- The factors in the Ct alternant are pairwise relatively prime; the row
factors enter through the determinant multilinearity identity above. -/
theorem paper_ct_full_factor_product_dvd {n : ℕ} (t : F) (ht : t ≠ 0) :
    paperCtFactorProduct (n := n) t ∣ paperCtAlternantPolynomial t := by
  classical
  have hcop := paper_ct_factor_pairwise_isRelPrime (n := n) t ht
  have hrowprod : (∏ a : Fin n, (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2)) ∣
      paperCtAlternantPolynomial t := by
    refine ⟨(Matrix.of fun a r : Fin n =>
      paperCtRowQuotient (MvPolynomial.C t) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)).det, ?_⟩
    simpa [paperCtAlternantPolynomial] using
      (paper_ct_determinant_extra_row_factors
        (R := MvPolynomial (Fin n) F) (t := MvPolynomial.C t)
        (z := MvPolynomial.X (R := F) (σ := Fin n)))
  apply Fintype.prod_dvd_of_isRelPrime hcop
  intro i
  cases i with
  | inl p =>
    by_cases hb : p.2
    · simp only [paperCtFactor, paperBasicFactor, hb]
      exact paper_ct_factor_dvd_any_pair t p.1.1 p.1.2.1
        (ne_of_lt p.1.2.2) ht
    · simp only [paperCtFactor, paperBasicFactor, hb]
      exact paper_ct_difference_factor_dvd_any_pair t p.1.1 p.1.2.1
        (ne_of_lt p.1.2.2)
  | inr a =>
    change (1 - MvPolynomial.C t * MvPolynomial.X a ^ 2) ∣ _
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun x : Fin n =>
        1 - MvPolynomial.C t * MvPolynomial.X x ^ 2) (Finset.mem_univ a)) hrowprod

theorem paper_bminus_difference_factor_dvd_any_pair {N : ℕ} (t : F)
    (a b : Fin N) (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin N) F) ∣
      paperBminusAlternantPolynomial t := by
  classical
  cases N with
  | zero => exact Fin.elim0 a
  | succ n =>
    let e : Equiv.Perm (Fin n.succ) := Equiv.swap 0 b
    have he0 : e 0 = b := by simp [e]
    have hEa : e.symm a ≠ 0 := by
      intro h
      have : a = b := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e 0 := by rw [h]
          _ = b := he0
      exact hab this
    have hval : 0 < (e.symm a).val := by
      by_contra! h
      have hv : (e.symm a).val = 0 := Nat.eq_zero_of_le_zero h
      exact hEa (Fin.ext hv)
    let j : Fin n := ⟨(e.symm a).val - 1, by have h := (e.symm a).isLt; omega⟩
    have hjs : j.succ = e.symm a := by
      apply Fin.ext
      change ((e.symm a).val - 1) + 1 = (e.symm a).val
      omega
    have hejs : e j.succ = a := by rw [hjs, e.apply_symm_apply]
    have hbase := paper_bminus_last_variable_difference_dvd (F := F) (n := n) t j
    let ρ : MvPolynomial (Fin n.succ) F →+* MvPolynomial (Fin n.succ) F :=
      (MvPolynomial.rename e).toRingHom
    let s : F := ((Equiv.Perm.sign e : ℤ) : F)
    have hrenameFactor : ρ (MvPolynomial.X 0 - MvPolynomial.X j.succ) =
        MvPolynomial.X b - MvPolynomial.X a := by
      change MvPolynomial.rename e (MvPolynomial.X 0 - MvPolynomial.X j.succ) = _
      simp [MvPolynomial.rename_X, hejs, he0]
    have hrenameAlternant :
        ρ (paperBminusAlternantPolynomial (F := F) (n := n.succ) t) =
        MvPolynomial.C s * paperBminusAlternantPolynomial (F := F) (n := n.succ) t := by
      rw [show paperBminusAlternantPolynomial (F := F) (n := n.succ) t =
        (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).det by rfl,
        RingHom.map_det]
      rw [show ρ.mapMatrix (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r =>
          bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) by
          apply Matrix.ext
          intro i r
          change MvPolynomial.rename e (bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i)) =
            bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i))
          simpa using map_bminusAlternantColumn (MvPolynomial.rename e).toRingHom
            (MvPolynomial.C t) r (MvPolynomial.X i)]
      rw [show (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X (e i) : MvPolynomial (Fin n.succ) F)) =
        (Matrix.of fun i r : Fin n.succ =>
          bminusAlternantColumn (MvPolynomial.C t) r (MvPolynomial.X i : MvPolynomial (Fin n.succ) F)).submatrix e id by
          ext i r
          rfl,
        Matrix.det_permute]
      simp [s]
    have hmapDvd := map_dvd ρ hbase
    rw [hrenameFactor, hrenameAlternant] at hmapDvd
    have hs : s ≠ 0 := by
      dsimp [s]
      rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]
    have hCs : (MvPolynomial.C (R := F) (σ := Fin n.succ) (s⁻¹)) *
        MvPolynomial.C (R := F) (σ := Fin n.succ) s = 1 := by
      rw [← MvPolynomial.C_mul, inv_mul_cancel₀ hs, MvPolynomial.C_1]
    obtain ⟨q, hq⟩ := hmapDvd
    refine ⟨-(MvPolynomial.C (s⁻¹) * q), ?_⟩
    calc
      paperBminusAlternantPolynomial (F := F) (n := n.succ) t =
          MvPolynomial.C (s⁻¹) * (MvPolynomial.C s * paperBminusAlternantPolynomial t) := by
        rw [← mul_assoc, hCs, one_mul]
      _ = MvPolynomial.C (s⁻¹) * ((MvPolynomial.X b - MvPolynomial.X a) * q) := by
        rw [← hq]
      _ = (MvPolynomial.X a - MvPolynomial.X b) *
          (-(MvPolynomial.C (s⁻¹) * q)) := by ring

/- The B₋ factor family is pairwise relatively prime, so the individual
divisibility statements combine by the paper's product step. -/
theorem paper_bminus_full_factor_product_dvd {n : ℕ} (τ : F) (hτ : τ ≠ 0) :
    paperBminusFactorProduct (n := n) τ ∣ paperBminusAlternantPolynomial τ := by
  classical
  have hcop := paper_bminus_factor_pairwise_isRelPrime (n := n) τ hτ
  have hrowprod : (∏ a : Fin n, (1 + MvPolynomial.C τ * MvPolynomial.X a)) ∣
      paperBminusAlternantPolynomial τ := by
    refine ⟨(Matrix.of fun a r : Fin n =>
      paperBminusRowQuotient (MvPolynomial.C τ) r
        (MvPolynomial.X a : MvPolynomial (Fin n) F)).det, ?_⟩
    simpa [paperBminusAlternantPolynomial] using
      (paper_bminus_determinant_extra_row_factors
        (R := MvPolynomial (Fin n) F) (τ := MvPolynomial.C τ)
        (z := MvPolynomial.X (R := F) (σ := Fin n)))
  apply Fintype.prod_dvd_of_isRelPrime hcop
  intro i
  cases i with
  | inl p =>
    by_cases hb : p.2
    · simp only [paperBminusFactor, paperBasicFactor, hb]
      exact paper_bminus_factor_dvd_any_pair τ p.1.1 p.1.2.1
        (ne_of_lt p.1.2.2) hτ
    · simp only [paperBminusFactor, paperBasicFactor, hb]
      exact paper_bminus_difference_factor_dvd_any_pair τ p.1.1 p.1.2.1
        (ne_of_lt p.1.2.2)
  | inr a =>
    change (1 + MvPolynomial.C τ * MvPolynomial.X a) ∣ _
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun x : Fin n =>
        (1 + MvPolynomial.C τ * MvPolynomial.X x)) (Finset.mem_univ a)) hrowprod

end
end AffineDualJT
