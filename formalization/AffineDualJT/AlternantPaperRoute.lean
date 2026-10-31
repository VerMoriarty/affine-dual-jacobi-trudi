import AffineDualJT.AlternantFactorization

/-!
# Proportional rows in the original proof of Lemma 2.1

Under the paper's reciprocal substitution, each pair of rows is proportional.
These lemmas record the three multipliers in the paper's indexing, before
using alternation to obtain the factors `1 - t*z_a*z_b`.
-/

namespace AffineDualJT

private theorem paper_det_zero_of_row_smul
    {F : Type*} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (a b : Fin n) (c : F)
    (hab : a ≠ b) (hc : c ≠ 0)
    (hrow : ∀ r, M b r = c * M a r) : M.det = 0 := by
  classical
  let w : Fin n → F := fun i => if i = b then c⁻¹ else 1
  let N : Matrix (Fin n) (Fin n) F := fun i r => w i * M i r
  have hrows : N a = N b := by
    funext r
    simp [N, w, hab, hrow r, hc]
  have hdet : N.det = 0 := Matrix.det_zero_of_row_eq hab hrows
  rw [show N = Matrix.of (fun i r => w i * M i r) by rfl,
    Matrix.det_mul_column] at hdet
  have hw : (∏ i : Fin n, w i) = c⁻¹ := by
    rw [Finset.prod_eq_single b]
    · simp [w]
    · intro i _ hib
      simp [w, hib]
    · simp [w]
  rw [hw] at hdet
  exact (mul_eq_zero.mp hdet).resolve_left (inv_ne_zero hc)

theorem paper_basic_row_proportional
    {F : Type*} [Field F] {n : ℕ}
    (t : F) (z : Fin n → F) (a b : Fin n) (_hab : a ≠ b)
    (ht : t ≠ 0) (ha : z a ≠ 0)
    (hzb : z b = (t * z a)⁻¹) (r : Fin n) :
    fColumn t r (z b) =
      (((t * z a)⁻¹)^(n-1) / (z a)^(n-1)) * fColumn t r (z a) := by
  have hb : z b ≠ 0 := by rw [hzb]; exact inv_ne_zero (mul_ne_zero ht ha)
  have harg : (z b)⁻¹ + t * z b = (z a)⁻¹ + t * z a := by
    rw [hzb]
    field_simp [ht, ha]
    ring
  rw [fColumn_row_factor t (z b) hb r, fColumn_row_factor t (z a) ha r, harg]
  have hfac : (z b)^(n-1) =
      (((t * z a)⁻¹)^(n-1) / (z a)^(n-1)) * (z a)^(n-1) := by
    rw [hzb]
    field_simp [ht, ha]
  rw [hfac]
  ring

theorem paper_ct_row_proportional
    {F : Type*} [Field F] {n : ℕ}
    (t : F) (z : Fin n → F) (a b : Fin n) (_hab : a ≠ b)
    (ht : t ≠ 0) (ha : z a ≠ 0) (hn : 0 < n)
    (hzb : z b = (t * z a)⁻¹) (r : Fin n) :
    ctAlternantColumn t r (z b) =
      (-((t * z a)⁻¹)^n / (z a)^n) * ctAlternantColumn t r (z a) := by
  have hb : z b ≠ 0 := by rw [hzb]; exact inv_ne_zero (mul_ne_zero ht ha)
  have harg : (z b)⁻¹ + t * z b = (z a)⁻¹ + t * z a := by
    rw [hzb]
    field_simp [ht, ha]
    ring
  rw [ctAlternantColumn_row_factor t (z b) hb r,
    ctAlternantColumn_row_factor t (z a) ha r, harg]
  have hfac : (z b)^(n-1) * (1-t*(z b)^2) =
      (-((t*z a)⁻¹)^n/(z a)^n) * ((z a)^(n-1)*(1-t*(z a)^2)) := by
    cases n with
    | zero => omega
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [hzb]
      simp only [pow_succ]
      simp only [inv_pow]
      field_simp [ht, ha]
      ring
  rw [hfac]
  ring

theorem paper_bminus_row_proportional
    {F : Type*} [Field F] {n : ℕ}
    (τ : F) (z : Fin n → F) (a b : Fin n) (_hab : a ≠ b)
    (hτ : τ ≠ 0) (ha : z a ≠ 0) (hn : 0 < n)
    (hzb : z b = (τ^2 * z a)⁻¹) (r : Fin n) :
    bminusAlternantColumn τ r (z b) =
      (τ * ((τ^2*z a)⁻¹)^n/(z a)^(n-1)) *
        bminusAlternantColumn τ r (z a) := by
  have hb : z b ≠ 0 := by rw [hzb]; exact inv_ne_zero (mul_ne_zero (pow_ne_zero 2 hτ) ha)
  have harg : (z b)⁻¹ + τ^2 * z b = (z a)⁻¹ + τ^2 * z a := by
    rw [hzb]
    field_simp [hτ, ha]
    ring
  rw [bminusAlternantColumn_row_factor τ (z b) hb r,
    bminusAlternantColumn_row_factor τ (z a) ha r, harg]
  have hfac : (z b)^(n-1) * (1+τ*z b) =
      (τ*((τ^2*z a)⁻¹)^n/(z a)^(n-1)) *
        ((z a)^(n-1)*(1+τ*z a)) := by
    cases n with
    | zero => omega
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [hzb]
      simp only [pow_succ]
      simp only [inv_pow]
      field_simp [hτ, ha]
      ring
  rw [hfac]
  ring

/-- The reciprocal substitution from the paper makes the two rows dependent;
this is the determinant-vanishing step that yields the factor `1-t*z_a*z_b`.
The factor-divisibility argument is developed separately from this local step. -/
theorem paper_basic_alternant_vanish_under_reciprocal
    {F : Type*} [Field F] {n : ℕ}
    (t : F) (z : Fin n → F) (a b : Fin n) (hab : a ≠ b)
    (ht : t ≠ 0) (ha : z a ≠ 0)
    (hzb : z b = (t * z a)⁻¹) :
    (Matrix.of fun i r => fColumn t r (z i) : Matrix (Fin n) (Fin n) F).det = 0 := by
  apply paper_det_zero_of_row_smul _ a b
    (((t * z a)⁻¹)^(n-1) / (z a)^(n-1)) hab ?_ ?_
  · exact div_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero ht ha)))
      (pow_ne_zero _ ha)
  · intro r
    exact paper_basic_row_proportional t z a b hab ht ha hzb r

theorem paper_ct_alternant_vanish_under_reciprocal
    {F : Type*} [Field F] {n : ℕ}
    (t : F) (z : Fin n → F) (a b : Fin n) (hab : a ≠ b)
    (ht : t ≠ 0) (ha : z a ≠ 0) (hn : 0 < n)
    (hzb : z b = (t * z a)⁻¹) :
    (Matrix.of fun i r => ctAlternantColumn t r (z i) : Matrix (Fin n) (Fin n) F).det = 0 := by
  apply paper_det_zero_of_row_smul _ a b
    (-((t * z a)⁻¹)^n / (z a)^n) hab ?_ ?_
  · exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero (mul_ne_zero ht ha))))
      (pow_ne_zero _ ha)
  · intro r
    exact paper_ct_row_proportional t z a b hab ht ha hn hzb r

theorem paper_bminus_alternant_vanish_under_reciprocal
    {F : Type*} [Field F] {n : ℕ}
    (τ : F) (z : Fin n → F) (a b : Fin n) (hab : a ≠ b)
    (hτ : τ ≠ 0) (ha : z a ≠ 0) (hn : 0 < n)
    (hzb : z b = (τ^2 * z a)⁻¹) :
    (Matrix.of fun i r => bminusAlternantColumn τ r (z i) : Matrix (Fin n) (Fin n) F).det = 0 := by
  apply paper_det_zero_of_row_smul _ a b
    (τ * ((τ^2 * z a)⁻¹)^n / (z a)^(n-1)) hab ?_ ?_
  · exact div_ne_zero (mul_ne_zero hτ
      (pow_ne_zero _ (inv_ne_zero (mul_ne_zero (pow_ne_zero 2 hτ) ha))))
      (pow_ne_zero _ ha)
  · intro r
    exact paper_bminus_row_proportional τ z a b hab hτ ha hn hzb r

end AffineDualJT
