import AffineDualJT.Basic

/-! # The affine determinant sum `J_K` (paper p.2, equation (1.2)). -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

namespace AffineDetSum
variable {R : Type*} [CommRing R]
variable {k : ℕ}

/-- §3.3: residue shifts preserve finite row support when `K≠0`. -/
theorem weighted_shift_hasFiniteSupport (K j : ℤ) (hK : K ≠ 0)
    (w F : ℤ → R) (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun y => w y * F (j - K * y)) := by
  have hinj : Function.Injective (fun y : ℤ => j - K * y) := by
    intro a b h
    change j - K * a = j - K * b at h
    have hmul : K * a = K * b := sub_right_inj.mp h
    exact mul_left_cancel₀ hK hmul
  exact Function.HasFiniteSupport.mul_right w (hF.fun_comp_of_injective hinj)

/-- Matrix occurring in one summand of (1.2). -/
def jkMatrix
    (K : ℤ) (w : Fin k → ℤ → R) (F : Fin k → ℤ → R)
    (y : Fin k → ℤ) : Matrix (Fin k) (Fin k) R :=
  fun i j => w j (y i) * F i (paperIndex j - K * y i)

/-- Paper p.2, equation (1.2), on the full lattice `ℤ^k`. -/
noncomputable def JK
    (K : ℤ) (w : Fin k → ℤ → R) (F : Fin k → ℤ → R) : R :=
  ∑ᶠ y : Fin k → ℤ, (jkMatrix K w F y).det

/-- The equation (1.2) determinant sum restricted to an arbitrary subset
`L ⊆ ℤ^k`.  `JK` and `JKEven` are the full-lattice and even-sublattice
instances, respectively. -/
noncomputable def JKOn
    (K : ℤ) (w : Fin k → ℤ → R) (F : Fin k → ℤ → R)
    (L : (Fin k → ℤ) → Prop) : R :=
  ∑ᶠ (y : Fin k → ℤ) (_hy : L y), (jkMatrix K w F y).det

/-- Restricting `JKOn` to the whole lattice recovers `JK`. -/
@[simp] theorem JKOn_univ (K : ℤ) (w F : Fin k → ℤ → R) :
    JKOn K w F (fun _ => True) = JK K w F := by
  simp [JKOn, JK]

/-- `ℤ^k_even` from p.2. -/
def EvenVector (y : Fin k → ℤ) : Prop := Even (∑ i : Fin k, y i)

/-- Equation (1.2) restricted to `ℤ^k_even`. -/
noncomputable def JKEven
    (K : ℤ) (w : Fin k → ℤ → R) (F : Fin k → ℤ → R) : R :=
  ∑ᶠ (y : Fin k → ℤ) (_hy : EvenVector y), (jkMatrix K w F y).det

/-- The paper's even-lattice sum is the corresponding instance of `JKOn`. -/
@[simp] theorem JKOn_even (K : ℤ) (w F : Fin k → ℤ → R) :
    JKOn K w F EvenVector = JKEven K w F := by
  rfl

/-- Empty determinant convention used on pp.2 and 13. -/
theorem det_fin_zero_eq_one (M : Matrix (Fin 0) (Fin 0) R) : M.det = 1 := by
  simp

/-- No entry or weight is evaluated when the width is zero, as in (1.2). -/
@[simp] theorem JK_zero (K : ℤ) (w F : Fin 0 → ℤ → R) : JK K w F = 1 := by
  let : Unique (Fin 0 → ℤ) :=
    ⟨⟨fun i => Fin.elim0 i⟩, fun _ => Subsingleton.elim _ _⟩
  simp [JK, finsum_unique]

/-- The empty vector belongs to the even sublattice. -/
@[simp] theorem evenVector_zero (y : Fin 0 → ℤ) : EvenVector y := by
  simp [EvenVector]

/-- The even-sublattice version has the same empty-determinant convention. -/
@[simp] theorem JKEven_zero (K : ℤ) (w F : Fin 0 → ℤ → R) : JKEven K w F = 1 := by
  let : Unique (Fin 0 → ℤ) :=
    ⟨⟨fun i => Fin.elim0 i⟩, fun _ => Subsingleton.elim _ _⟩
  simp [JKEven, finsum_unique]

end AffineDetSum
end
end AffineDualJT
