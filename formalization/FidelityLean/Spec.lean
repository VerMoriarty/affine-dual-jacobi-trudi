import Mathlib

/-!
Independent specification extracted from authoritative.pdf, pp. 1--15.
No implementation module is imported. All named assertions below are `Prop`
definitions, not axioms and not proofs of the paper.

`paperIndex i = i.val + 1` translates the paper's one-based indices. Coefficient
indices are integers. `finsum` records the paper's finite integer sums without
requiring an arbitrary truncation. Separate finite-support obligations are
exposed below. The raw equality interfaces are intended over the paper's
rational-function field; `WeylRegular` states the hypotheses for direct numeric
evaluation of the uncancelled Weyl expression. Removable singularities require
cancellation before evaluation, as on p. 14 of the paper.
-/

noncomputable section

open scoped BigOperators

namespace Fidelity.Spec

abbrev ParameterField (n : ℕ) :=
  FractionRing (MvPolynomial (Fin (n + 1)) ℚ)

def symbolicVariable (n : ℕ) (i : Fin (n + 1)) : ParameterField n :=
  algebraMap (MvPolynomial (Fin (n + 1)) ℚ) (ParameterField n) (MvPolynomial.X i)

theorem symbolicVariable_ne_zero (n : ℕ) (i : Fin (n + 1)) :
    symbolicVariable n i ≠ 0 := by
  intro h
  have hx : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℚ) = 0 :=
    (IsFractionRing.to_map_eq_zero_iff).mp h
  exact MvPolynomial.X_ne_zero i hx

/-- Slot zero is t, or tau in the two square-root cases. -/
def symbolicParameter (n : ℕ) : ParameterField n := symbolicVariable n 0

/-- Slots 1,...,n are invertible independent Laurent variables. -/
def symbolicX (n : ℕ) (a : Fin n) : (ParameterField n)ˣ :=
  Units.mk0 (symbolicVariable n ⟨a.val + 1, by omega⟩)
    (symbolicVariable_ne_zero n ⟨a.val + 1, by omega⟩)

def paperIndex {m : ℕ} (i : Fin m) : ℤ := (i.val : ℤ) + 1

inductive PaperCase
  | C0 | Ct | BC | B0 | Bminus | Bplus | Bt
  deriving DecidableEq, Repr

instance : Fintype PaperCase where
  elems := {.C0, .Ct, .BC, .B0, .Bminus, .Bplus, .Bt}
  complete := by intro c; cases c <;> simp

inductive Folding
  | C | B | plus
  deriving DecidableEq, Repr

instance : Fintype Folding where
  elems := {.C, .B, .plus}
  complete := by intro d; cases d <;> simp

local instance (p : Prop) : Decidable p := Classical.propDecidable p

section Coefficients

variable {F : Type*} [Field F]

def Edot {n : ℕ} (x : Fin n → Fˣ) : Polynomial F :=
  ∏ a, (1 + Polynomial.C (x a : F) * Polynomial.X) *
    (1 + Polynomial.C ((x a : F)⁻¹) * Polynomial.X)

def Eddot {n : ℕ} (x : Fin n → Fˣ) : Polynomial F :=
  (1 + Polynomial.X) * Edot x

def dotCoeff {n : ℕ} (x : Fin n → Fˣ) (r : ℤ) : F :=
  if 0 ≤ r ∧ r ≤ 2 * (n : ℤ) then (Edot x).coeff r.toNat else 0

def ddotCoeff {n : ℕ} (x : Fin n → Fˣ) (r : ℤ) : F :=
  if 0 ≤ r ∧ r ≤ 2 * (n : ℤ) + 1 then (Eddot x).coeff r.toNat else 0

def lambdaKernel {n k : ℕ} (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) : F :=
  dotCoeff x ((n : ℤ) - paperIndex i + m) -
    dotCoeff x ((n : ℤ) + paperIndex i + m)

def hKernel {n k : ℕ} (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) : F :=
  dotCoeff x ((n : ℤ) - paperIndex i + m) +
    dotCoeff x ((n : ℤ) + paperIndex i + m - 1)

def hPlusKernel {n k : ℕ} (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) : F :=
  dotCoeff x ((n : ℤ) - paperIndex i + m) +
    dotCoeff x ((n : ℤ) + paperIndex i + m - 2)

def hHatKernel {n k : ℕ} (x : Fin n → Fˣ) (i : Fin k) (m : ℤ) : F :=
  ddotCoeff x ((n : ℤ) - paperIndex i + m) +
    ddotCoeff x ((n : ℤ) + paperIndex i + m - 1)

def sign (m : ℤ) : F := (-1 : F) ^ m

def jIntegrand {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (row : Fin k → ℤ → F) (y : Fin k → ℤ) : F :=
  Matrix.det (fun i j => w j (y i) * row i (paperIndex j - K * y i))

def JK {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (row : Fin k → ℤ → F) : F :=
  finsum (jIntegrand K w row)

def EvenLattice {k : ℕ} (y : Fin k → ℤ) : Prop := Even (∑ i, y i)

def JKEven {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (row : Fin k → ℤ → F) : F :=
  finsum (fun y : Fin k → ℤ =>
    if EvenLattice y then jIntegrand K w row y else 0)

def JKOn {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (row : Fin k → ℤ → F) (lattice : Set (Fin k → ℤ)) : F :=
  finsum (fun y : Fin k → ℤ =>
    if y ∈ lattice then jIntegrand K w row y else 0)

def AffineFiniteSupport {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (row : Fin k → ℤ → F) : Prop :=
  (Function.support (jIntegrand K w row)).Finite

def CoefficientConventions {n : ℕ} (x : Fin n → Fˣ) : Prop :=
  (∀ r : ℤ, dotCoeff x (2 * (n : ℤ) - r) = dotCoeff x r) ∧
  (∀ r : ℤ, ddotCoeff x (2 * (n : ℤ) + 1 - r) = ddotCoeff x r) ∧
  (∀ r : ℤ, ddotCoeff x r = dotCoeff x r + dotCoeff x (r - 1))

end Coefficients

section WeylDefinition

variable {F : Type*} [Field F]

def parameter (c : PaperCase) (t tau : F) : F :=
  match c with
  | .BC | .Bminus => tau ^ 2
  | _ => t

def rho (c : PaperCase) (t tau z : F) : F :=
  match c with
  | .C0 => (1 - z ^ 2)⁻¹
  | .Ct => (1 - t * z ^ 2) / (1 - z ^ 2)
  | .BC => (1 + tau * z) / (1 - z ^ 2)
  | .B0 => (1 - z)⁻¹
  | .Bminus => (1 + tau * z) / (1 - z)
  | .Bplus => 1
  | .Bt => (1 - t * z) / (1 - z)

def nuZero (c : PaperCase) (n : ℕ) (t tau : F) : F :=
  match c with
  | .C0 | .BC | .B0 => 1
  | .Ct | .Bt => ∏ r : Fin n, (1 + t ^ (r.val + 1))
  | .Bminus => ∏ r : Fin n, (1 - tau ^ (2 * r.val + 1))
  | .Bplus => ∏ r : Fin n, (1 + t ^ r.val)

def nu (c : PaperCase) (n k : ℕ) (t tau : F) : F :=
  if k = 0 then nuZero c n t tau else 1

def Vn (n : ℕ) (t : F) : F :=
  ∏ r : Fin n, ∑ s ∈ Finset.range (r.val + 1), t ^ s

abbrev SignedPermutation (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool)

def weylPoint {n : ℕ} (x : Fin n → Fˣ) (w : SignedPermutation n)
    (a : Fin n) : F :=
  if w.2 a then (x (w.1 a) : F)⁻¹ else (x (w.1 a) : F)

def weylPairProduct {n : ℕ} (t : F) (u : Fin n → F) : F :=
  ∏ a : Fin n, ∏ b : Fin n,
    if a.val < b.val then
      ((t * u a - u b) * (1 - t * u a * u b)) /
        ((u a - u b) * (1 - u a * u b))
    else 1

def weylSummand {n : ℕ} (c : PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) (w : SignedPermutation n) : F :=
  let tp := parameter c t tau
  let u := weylPoint x w
  (∏ a : Fin n, (u a) ^ (-(k : ℤ)) * rho c tp tau (u a)) *
    weylPairProduct tp u

/-- Equation (2.1), independent of every affine determinant. -/
def P {n : ℕ} (c : PaperCase) (k : ℕ) (x : Fin n → Fˣ)
    (t tau : F) : F :=
  (∑ w : SignedPermutation n, weylSummand c k x t tau w) /
    (Vn n (parameter c t tau) * nu c n k (parameter c t tau) tau)

def WeylRegular {n : ℕ} (c : PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) : Prop :=
  Vn n (parameter c t tau) * nu c n k (parameter c t tau) tau ≠ 0 ∧
  ∀ w : SignedPermutation n,
    (∀ a, (match c with
      | .C0 | .Ct | .BC => 1 - (weylPoint x w a) ^ 2
      | .B0 | .Bminus | .Bt => 1 - weylPoint x w a
      | .Bplus => 1) ≠ (0 : F)) ∧
    ∀ a b : Fin n, a.val < b.val →
      ((weylPoint x w a - weylPoint x w b) *
        (1 - weylPoint x w a * weylPoint x w b)) ≠ 0

end WeylDefinition

section MainIdentities

variable {F : Type*} [Field F]

def expB0 {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  (k : ℤ) * y ^ 2 + (y ^ 2 + y) / 2 - paperIndex j * y

def expBminus {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  2 * (k : ℤ) * y ^ 2 - (2 * paperIndex j - 1) * y

def expBplus {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  (k : ℤ) * y ^ 2 - (paperIndex j - 1) * y

def expC0 {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  ((k : ℤ) + 1) * y ^ 2 - paperIndex j * y

def expCt {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  (k : ℤ) * y ^ 2 - paperIndex j * y

def expBC {k : ℕ} (j : Fin k) (y : ℤ) : ℤ :=
  (2 * (k : ℤ) + 1) * y ^ 2 - 2 * paperIndex j * y

def weightB0 {k : ℕ} (t : F) (j : Fin k) (y : ℤ) : F :=
  sign y * t ^ expB0 j y

def weightBminus {k : ℕ} (tau : F) (j : Fin k) (y : ℤ) : F :=
  tau ^ expBminus j y

def weightBplus {k : ℕ} (t : F) (j : Fin k) (y : ℤ) : F :=
  sign y * t ^ expBplus j y

def weightC0 {k : ℕ} (t : F) (j : Fin k) (y : ℤ) : F := t ^ expC0 j y

def weightCt {k : ℕ} (t : F) (j : Fin k) (y : ℤ) : F := t ^ expCt j y

def weightBC {k : ℕ} (tau : F) (j : Fin k) (y : ℤ) : F :=
  sign y * tau ^ expBC j y

def MainA13 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  P .B0 k x t 0 = JK (k := k) (2 * (k : ℤ) + 1) (weightB0 t) (hKernel x)

def MainA14 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (tau : F) : Prop :=
  P .Bminus k x 0 tau = JK (k := k) (2 * (k : ℤ)) (weightBminus tau) (hKernel x)

def MainA15 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  P .Bplus k x t 0 = (2 : F)⁻¹ *
    JK (k := k) (2 * (k : ℤ)) (weightBplus t) (hPlusKernel x)

def MainA16 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  P .C0 k x t 0 = JK (k := k) (2 * (k : ℤ) + 2) (weightC0 t) (lambdaKernel x)

def MainA17 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  P .Ct k x t 0 = JKEven (k := k) (2 * (k : ℤ)) (weightCt t) (lambdaKernel x)

def MainA18 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (tau : F) : Prop :=
  P .BC k x 0 tau = JK (k := k) (2 * (k : ℤ) + 1) (weightBC tau) (lambdaKernel x)

def MainB19 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  P .Bt k x t 0 = (2 : F)⁻¹ *
    JK (k := k) (2 * (k : ℤ)) (weightBplus t) (hHatKernel x)

def TheoremAInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t tau : F) : Prop :=
  0 < n →
    MainA13 k x t ∧ MainA14 k x tau ∧ (0 < k → MainA15 k x t) ∧
    MainA16 k x t ∧ MainA17 k x t ∧ MainA18 k x tau ∧
    P .Bplus 0 x t 0 = 1

def TheoremBInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  0 < n → (0 < k → MainB19 k x t) ∧ P .Bt 0 x t 0 = 1

def WidthZero {n : ℕ} (c : PaperCase) (x : Fin n → Fˣ) (t tau : F) : Prop :=
  P c 0 x t tau = 1

def WidthZeroC0 {n : ℕ} (x : Fin n → Fˣ) (t : F) : Prop :=
  WidthZero .C0 x t 0
def WidthZeroCt {n : ℕ} (x : Fin n → Fˣ) (t : F) : Prop :=
  WidthZero .Ct x t 0
def WidthZeroBC {n : ℕ} (x : Fin n → Fˣ) (tau : F) : Prop :=
  WidthZero .BC x 0 tau
def WidthZeroB0 {n : ℕ} (x : Fin n → Fˣ) (t : F) : Prop :=
  WidthZero .B0 x t 0
def WidthZeroBminus {n : ℕ} (x : Fin n → Fˣ) (tau : F) : Prop :=
  WidthZero .Bminus x 0 tau
def WidthZeroBplus {n : ℕ} (x : Fin n → Fˣ) (t : F) : Prop :=
  WidthZero .Bplus x t 0
def WidthZeroBt {n : ℕ} (x : Fin n → Fˣ) (t : F) : Prop :=
  WidthZero .Bt x t 0

def Proposition61Interface {n : ℕ} (x : Fin n → Fˣ) (t tau : F) : Prop :=
  0 < n → ∀ c : PaperCase, WidthZero c x t tau

def AffineFiniteSupportInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t tau : F) : Prop :=
  0 < n →
  AffineFiniteSupport (k := k) (2 * (k : ℤ) + 1) (weightB0 t) (hKernel x) ∧
  AffineFiniteSupport (k := k) (2 * (k : ℤ)) (weightBminus tau) (hKernel x) ∧
  AffineFiniteSupport (k := k) (2 * (k : ℤ) + 2) (weightC0 t) (lambdaKernel x) ∧
  AffineFiniteSupport (k := k) (2 * (k : ℤ)) (weightCt t) (lambdaKernel x) ∧
  AffineFiniteSupport (k := k) (2 * (k : ℤ) + 1) (weightBC tau) (lambdaKernel x) ∧
  (0 < k →
    AffineFiniteSupport (k := k) (2 * (k : ℤ)) (weightBplus t) (hPlusKernel x) ∧
    AffineFiniteSupport (k := k) (2 * (k : ℤ)) (weightBplus t) (hHatKernel x))

def ParameterExponentsInterface (k : ℕ) : Prop :=
  ∀ (j : Fin k) (y : ℤ),
    0 ≤ expB0 j y ∧ 0 ≤ expBminus j y ∧ 0 ≤ expBplus j y ∧
    0 ≤ expC0 j y ∧ 0 ≤ expCt j y ∧ 0 ≤ expBC j y

def EmptyAffineInterface : Prop :=
  ∀ (K : ℤ) (w row : Fin 0 → ℤ → F),
    JK K w row = 1 ∧ JKEven K w row = 1

end MainIdentities

section FiniteMatrices

variable {F : Type*} [Field F]

def phi (m : ℤ) (z : F) : F := z ^ m - z ^ (-m)
def psi (m : ℤ) (z : F) : F := z ^ m - z ^ (1 - m)
def cosine (m : ℤ) (z : F) : F := z ^ m + z ^ (-m)

def basis (L : ℕ) (m : ℤ) : Fin L → F :=
  fun p => if paperIndex p = m then 1 else 0

def bracket (d : Folding) (L : ℕ) (m : ℤ) : Fin L → F :=
  match d with
  | .C => if 0 < m then basis L m else
      if m = 0 then 0 else -basis L (-m)
  | .B => if 1 ≤ m then basis L m else -basis L (1 - m)
  | .plus => if 2 ≤ m then basis L m else
      if m = 1 then (fun p => 2 * basis L 1 p) else basis L (2 - m)

def caseFolding (c : PaperCase) : Folding :=
  match c with
  | .C0 | .Ct | .BC => .C
  | .B0 | .Bminus | .Bt => .B
  | .Bplus => .plus

def Phi {n k : ℕ} (d : Folding) (x : Fin n → Fˣ) :
    Matrix (Fin n) (Fin (n + k)) F :=
  fun a p => match d with
  | .C => phi (paperIndex p) (x a : F)
  | .B => psi (paperIndex p) (x a : F)
  | .plus => if p.val = 0 then 1 else cosine (p.val : ℤ) (x a : F)

def initial (n k : ℕ) (a : Fin n) : Fin (n + k) := ⟨a.val, by omega⟩
def tailJ (n k : ℕ) (i : Fin k) : Fin (n + k) := ⟨n + i.val, by omega⟩
def tailH (n k : ℕ) (a : Fin n) : Fin (n + k) := ⟨k + a.val, by omega⟩
def firstI (n k : ℕ) (i : Fin k) : Fin (n + k) := ⟨i.val, by omega⟩

def Delta {n : ℕ} (d : Folding) (x : Fin n → Fˣ) : F :=
  Matrix.det (Phi (k := 0) d x)

def columnU {n : ℕ} (d : Folding) (k : ℕ) (t : F) (r : Fin n) :
    Fin (n + k) → F :=
  if r.val = 0 then bracket d (n + k) ((k : ℤ) + 1) else
    fun p => bracket d (n + k) ((k : ℤ) + paperIndex r) p +
      t ^ r.val * bracket d (n + k) ((k : ℤ) + 2 - paperIndex r) p

def columnUTilde {n : ℕ} (d : Folding) (k : ℕ) (t : F) (r : Fin n) :
    Fin (n + k) → F :=
  if r.val = 0 then bracket d (n + k) (k : ℤ) else
    fun p => bracket d (n + k) ((k : ℤ) + paperIndex r - 1) p +
      t ^ r.val * bracket d (n + k) ((k : ℤ) + 1 - paperIndex r) p

def V {n : ℕ} (c : PaperCase) (k : ℕ) (t tau : F) :
    Matrix (Fin (n + k)) (Fin n) F :=
  fun p r =>
    let tp := parameter c t tau
    match c with
    | .C0 => columnU .C k tp r p
    | .Ct => bracket .C (n + k) ((k : ℤ) + paperIndex r) p -
        tp ^ (r.val + 1) * bracket .C (n + k) ((k : ℤ) - paperIndex r) p
    | .BC => columnU .C k tp r p + tau * columnUTilde .C k tp r p
    | .B0 => columnU .B k tp r p
    | .Bminus => bracket .B (n + k) ((k : ℤ) + paperIndex r) p +
        tau ^ (2 * r.val + 1) *
          bracket .B (n + k) ((k : ℤ) + 1 - paperIndex r) p
    | .Bplus => columnU .plus k tp r p
    | .Bt => columnU .B k tp r p - tp * columnUTilde .B k tp r p

def D {n k : ℕ} (d : Folding) (x : Fin n → Fˣ) :
    Matrix (Fin (n + k)) (Fin k) F :=
  fun p i => sign (paperIndex p) *
    (match d with
    | .C => lambdaKernel x i (paperIndex p)
    | .B => hKernel x i (paperIndex p)
    | .plus => hPlusKernel x i (paperIndex p))

def foldedSequence (d : Folding) (L : ℕ) {k : ℕ}
    (b : Fin k → ℤ → F) : Matrix (Fin L) (Fin k) F :=
  fun p j => match d with
  | .C => b j (paperIndex p) - b j (-paperIndex p)
  | .B => sign (paperIndex p) * (b j (paperIndex p) + b j (1 - paperIndex p))
  | .plus => if p.val = 0 then -b j 1 else
      sign (paperIndex p) * (b j (paperIndex p) + b j (2 - paperIndex p))

def omega (k : ℕ) : F := (-1 : F) ^ (k * (k + 1) / 2)
def zeta (n k : ℕ) : F := (-1 : F) ^ (n * k) * omega k

def FiniteRatio {n : ℕ} (c : PaperCase) (k : ℕ)
    (x : Fin n → Fˣ) (t tau : F) : Prop :=
  P c k x t tau = Matrix.det (Phi (k := k) (caseFolding c) x * V c k t tau) /
    Delta (caseFolding c) x

def FiniteMinor {n : ℕ} (c : PaperCase) (k : ℕ) (t tau : F) : Prop :=
  Matrix.det ((V (n := n) c k t tau).submatrix (tailH n k) id) = 1

def Proposition22Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t tau : F) : Prop :=
  0 < n → 0 < k → ∀ c : PaperCase,
    FiniteRatio c k x t tau ∧ FiniteMinor (n := n) c k t tau

def Theorem31Interface (n k : ℕ) : Prop :=
  0 < n → 0 < k → ∀ (X : Matrix (Fin n) (Fin (n + k)) F)
    (Y : Matrix (Fin (n + k)) (Fin n) F)
    (U Z : Matrix (Fin (n + k)) (Fin k) F),
  X * U = 0 → Y.transpose * Z = 0 →
  Matrix.det (X.submatrix id (initial n k)) ≠ 0 →
  Matrix.det (U.submatrix (tailJ n k) id) ≠ 0 →
  Matrix.det (Y.submatrix (tailH n k) id) ≠ 0 →
  Matrix.det (Z.submatrix (firstI n k) id) ≠ 0 →
  Matrix.det (X * Y) =
    ((-1 : F) ^ (n * k) * Matrix.det (X.submatrix id (initial n k)) *
      Matrix.det (Y.submatrix (tailH n k) id)) /
    (Matrix.det (U.submatrix (tailJ n k) id) *
      Matrix.det (Z.submatrix (firstI n k) id)) * Matrix.det (U.transpose * Z)

def Lemma32Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  0 < n → 0 < k →
  (∀ d : Folding, Phi (k := k) d x * D (k := k) d x = 0) ∧
  Matrix.det ((D (k := k) .C x).submatrix (tailJ n k) id) = zeta n k ∧
  Matrix.det ((D (k := k) .B x).submatrix (tailJ n k) id) = zeta n k ∧
  Matrix.det ((D (k := k) .plus x).submatrix (tailJ n k) id) = 2 * zeta n k

def Lemma33Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (b : Fin k → ℤ → F) : Prop :=
  0 < n → 0 < k → ∀ i j : Fin k,
  ((D (k := k) .C x).transpose * foldedSequence .C (n + k) b) i j =
    finsum (fun m : ℤ => sign m * lambdaKernel x i m * b j m) ∧
  ((D (k := k) .B x).transpose * foldedSequence .B (n + k) b) i j =
    finsum (fun m : ℤ => hKernel x i m * b j m) ∧
  ((D (k := k) .plus x).transpose * foldedSequence .plus (n + k) b) i j =
    finsum (fun m : ℤ => hPlusKernel x i m * b j m)

end FiniteMatrices

section Alternants

variable {F : Type*} [Field F]

def Nt {n : ℕ} (t : F) (z : Fin n → F) : F :=
  ∏ a : Fin n, ∏ b : Fin n,
    if a.val < b.val then (z a - z b) * (1 - t * z a * z b) else 1

def fColumn {n : ℕ} (t z : F) (r : Fin n) : F :=
  if r.val = 0 then z ^ (n - 1) else
    z ^ (n - (r.val + 1)) + t ^ r.val * z ^ (n + r.val - 1)

def Lemma21Interface {n : ℕ} (t tau : F) (z : Fin n → F) : Prop :=
  0 < n →
  Matrix.det (fun a r => fColumn t (z a) r) = Nt t z ∧
  Matrix.det (fun a r : Fin n =>
    (z a) ^ (n - (r.val + 1)) - t ^ (r.val + 1) * (z a) ^ (n + r.val + 1)) =
      (∏ a, (1 - t * (z a) ^ 2)) * Nt t z ∧
  Matrix.det (fun a r : Fin n =>
    (z a) ^ (n - (r.val + 1)) + tau ^ (2 * r.val + 1) * (z a) ^ (n + r.val)) =
      (∏ a, (1 + tau * z a)) * Nt (tau ^ 2) z

end Alternants

section AffineSequences

variable {F : Type*} [Field F]

def residueSequence {k : ℕ} (K : ℤ) (w : Fin k → ℤ → F)
    (j : Fin k) (m : ℤ) : F :=
  if (paperIndex j - m) % K = 0 then w j ((paperIndex j - m) / K) else 0

def sequence51 {k : ℕ} (t : F) : Fin k → ℤ → F :=
  residueSequence (2 * (k : ℤ)) (weightBplus t)

def Gamma {k : ℕ} (t : F) (j : Fin k) (m : ℤ) : F :=
  sign m * (sequence51 t j m + sequence51 t j (2 - m))

def adjacentSequence {k : ℕ} (t : F) (j : Fin k) (m : ℤ) : F :=
  sequence51 t j m + sequence51 t j (m + 1)

def adjacentC {k : ℕ} (t : F) (j : Fin k) (m : ℤ) : F :=
  sign m * (adjacentSequence t j m + adjacentSequence t j (1 - m))

def adjacentGamma {k : ℕ} (t : F) (j : Fin k) (m : ℤ) : F :=
  adjacentC t j m - t * adjacentC t j (m - 1)

def Lemma52Interface (k : ℕ) (t : F) : Prop :=
  0 < k → t ≠ 0 → ∀ j : Fin k,
    (∀ m : ℤ, sequence51 t j (m + 2 * (k : ℤ)) =
      -t ^ (m + (k : ℤ) - 1) * sequence51 t j m) ∧
    (∀ m : ℤ, Gamma t j (2 - m) = Gamma t j m) ∧
    (∀ m : ℤ, Gamma t j m =
      -t ^ (m - (k : ℤ) - 1) * Gamma t j (2 * (k : ℤ) + 2 - m)) ∧
    Gamma t j ((k : ℤ) + 1) = 0

def Lemma54Interface (k : ℕ) (t : F) : Prop :=
  0 < k → t ≠ 0 → ∀ j : Fin k,
    (∀ m : ℤ, adjacentC t j m = Gamma t j m - Gamma t j (m + 1)) ∧
    (∀ m : ℤ, adjacentGamma t j m =
      (1 + t) * Gamma t j m - Gamma t j (m + 1) - t * Gamma t j (m - 1)) ∧
    (∀ m : ℤ, adjacentGamma t j m =
      -t ^ (m - (k : ℤ) - 1) * adjacentGamma t j (2 * (k : ℤ) + 2 - m)) ∧
    adjacentGamma t j ((k : ℤ) + 1) = 0

def Proposition41Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t tau : F) : Prop :=
  0 < n → 0 < k → MainA16 k x t ∧ MainA18 k x tau

def Proposition42Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t tau : F) : Prop :=
  0 < n → 0 < k → MainA13 k x t ∧ MainA14 k x tau

def Proposition51Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t : F) : Prop :=
  0 < n → 0 < k → MainA17 k x t

def Proposition53Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t : F) : Prop :=
  0 < n → 0 < k → MainA15 k x t

def Proposition55Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t : F) : Prop :=
  0 < n → 0 < k → MainB19 k x t

def CtParityInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) (t : F) : Prop :=
  let a : Fin k → Fin k → ℤ → F :=
    fun i j y => weightCt t j y * lambdaKernel x i (paperIndex j - 2 * (k : ℤ) * y)
  let Aplus : Matrix (Fin k) (Fin k) F := fun i j => finsum (a i j)
  let Aminus : Matrix (Fin k) (Fin k) F :=
    fun i j => finsum (fun y : ℤ => sign y * a i j y)
  0 < n → ∀ hk : 0 < k,
    JKEven (k := k) (2 * (k : ℤ)) (weightCt t) (lambdaKernel x) =
      (2 : F)⁻¹ * (Matrix.det Aplus + Matrix.det Aminus) ∧
    (∀ i : Fin k, Aplus i ⟨k - 1, by omega⟩ = 0)

def ctSequence {k : ℕ} (t : F) : Fin k → ℤ → F :=
  residueSequence (2 * (k : ℤ)) (fun j y => sign y * weightCt t j y)

def CtComplementaryInterface {n : ℕ} (k : ℕ) (_x : Fin n → Fˣ)
    (t : F) : Prop :=
  let C : Matrix (Fin (n + k)) (Fin k) F := foldedSequence .C (n + k) (ctSequence t)
  0 < n → ∀ hk : 0 < k,
    (V (n := n) .Ct k t 0).transpose * C = 0 ∧
    Matrix.det (C.submatrix (firstI n k) id) = 2 ∧
    ∀ q : ℤ,
      let last : Fin k := ⟨k - 1, by omega⟩
      let m := (k : ℤ) + 2 * (k : ℤ) * q
      ctSequence t last m - ctSequence t last (-m) =
        2 * sign q * t ^ ((k : ℤ) * q * (q + 1))

def BplusComplementaryInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t : F) : Prop :=
  let C : Matrix (Fin (n + k)) (Fin k) F := foldedSequence .plus (n + k) (sequence51 t)
  0 < n → 0 < k →
    (V (n := n) .Bplus k t 0).transpose * C = 0 ∧
    Matrix.det (C.submatrix (firstI n k) id) = omega k ∧
    Matrix.det ((D (k := k) .plus x).submatrix (tailJ n k) id) = 2 * zeta n k

def BtComplementaryInterface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ)
    (t : F) : Prop :=
  let C : Matrix (Fin (n + k)) (Fin k) F := foldedSequence .B (n + k) (adjacentSequence t)
  0 < n → 0 < k →
    (V (n := n) .Bt k t 0).transpose * C = 0 ∧
    Matrix.det (C.submatrix (firstI n k) id) = 2 * omega k ∧
    Matrix.det ((D (k := k) .B x).submatrix (tailJ n k) id) = zeta n k

end AffineSequences

section ClassicalSpecialization

variable {F : Type*} [Field F]

def classicalNumerator {n : ℕ} (d : Folding) (k : ℕ) (x : Fin n → Fˣ) : F :=
  Matrix.det (fun a r : Fin n => match d with
    | .C => phi ((k : ℤ) + paperIndex r) (x a : F)
    | .B => psi ((k : ℤ) + paperIndex r) (x a : F)
    | .plus => cosine ((k : ℤ) + paperIndex r - 1) (x a : F))

def Classical61 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  classicalNumerator .C k x / Delta .C x =
    Matrix.det (fun i j : Fin k => lambdaKernel x i (paperIndex j))

def Classical62h {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  classicalNumerator .B k x / Delta .B x =
    Matrix.det (fun i j : Fin k => hKernel x i (paperIndex j))

def Classical62hHat {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  classicalNumerator .B k x / Delta .B x =
    (2 : F)⁻¹ * Matrix.det (fun i j : Fin k => hHatKernel x i (paperIndex j))

def Classical63 {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  classicalNumerator .plus k x / Delta .plus x =
    (2 : F)⁻¹ * Matrix.det (fun i j : Fin k => hPlusKernel x i (paperIndex j))

def Corollary62Interface {n : ℕ} (k : ℕ) (x : Fin n → Fˣ) : Prop :=
  0 < n → 0 < k →
    Classical61 k x ∧ Classical62h k x ∧ Classical62hHat k x ∧ Classical63 k x

end ClassicalSpecialization

/- Canonical paper statements have exactly the paper's n/k side conditions.
   They cannot acquire hidden numeric regularity hypotheses. -/
def StatementA13 (n k : ℕ) : Prop :=
  0 < n → MainA13 k (symbolicX n) (symbolicParameter n)
def StatementA14 (n k : ℕ) : Prop :=
  0 < n → MainA14 k (symbolicX n) (symbolicParameter n)
def StatementA15 (n k : ℕ) : Prop :=
  0 < n → 0 < k → MainA15 k (symbolicX n) (symbolicParameter n)
def StatementA16 (n k : ℕ) : Prop :=
  0 < n → MainA16 k (symbolicX n) (symbolicParameter n)
def StatementA17 (n k : ℕ) : Prop :=
  0 < n → MainA17 k (symbolicX n) (symbolicParameter n)
def StatementA18 (n k : ℕ) : Prop :=
  0 < n → MainA18 k (symbolicX n) (symbolicParameter n)
def StatementB19 (n k : ℕ) : Prop :=
  0 < n → 0 < k → MainB19 k (symbolicX n) (symbolicParameter n)

def StatementWidthZero (c : PaperCase) (n : ℕ) : Prop :=
  0 < n → WidthZero c (symbolicX n) (symbolicParameter n) (symbolicParameter n)

def StatementClassical61 (n k : ℕ) : Prop :=
  0 < n → 0 < k → Classical61 k (symbolicX n)
def StatementClassical62h (n k : ℕ) : Prop :=
  0 < n → 0 < k → Classical62h k (symbolicX n)
def StatementClassical62hHat (n k : ℕ) : Prop :=
  0 < n → 0 < k → Classical62hHat k (symbolicX n)
def StatementClassical63 (n k : ℕ) : Prop :=
  0 < n → 0 < k → Classical63 k (symbolicX n)

def StatementTheoremA (n k : ℕ) : Prop :=
  TheoremAInterface k (symbolicX n) (symbolicParameter n) (symbolicParameter n)
def StatementTheoremB (n k : ℕ) : Prop :=
  TheoremBInterface k (symbolicX n) (symbolicParameter n)

def StatementLemma21 (n : ℕ) : Prop :=
  Lemma21Interface (symbolicParameter n) (symbolicParameter n)
    (fun a : Fin n => (symbolicX n a : ParameterField n))
def StatementProposition22 (n k : ℕ) : Prop :=
  Proposition22Interface k (symbolicX n) (symbolicParameter n) (symbolicParameter n)
def StatementTheorem31 (n k : ℕ) : Prop :=
  ∀ (F : Type) (field : Field F), @Theorem31Interface F field n k
def StatementLemma32 (n k : ℕ) : Prop := Lemma32Interface k (symbolicX n)
def StatementLemma33 (n k : ℕ) (b : Fin k → ℤ → ParameterField n) : Prop :=
  Lemma33Interface k (symbolicX n) b
def StatementProposition41 (n k : ℕ) : Prop :=
  Proposition41Interface k (symbolicX n) (symbolicParameter n) (symbolicParameter n)
def StatementProposition42 (n k : ℕ) : Prop :=
  Proposition42Interface k (symbolicX n) (symbolicParameter n) (symbolicParameter n)
def StatementProposition51 (n k : ℕ) : Prop :=
  Proposition51Interface k (symbolicX n) (symbolicParameter n)
def StatementLemma52 (n k : ℕ) : Prop :=
  Lemma52Interface k (symbolicParameter n)
def StatementProposition53 (n k : ℕ) : Prop :=
  Proposition53Interface k (symbolicX n) (symbolicParameter n)
def StatementLemma54 (n k : ℕ) : Prop :=
  Lemma54Interface k (symbolicParameter n)
def StatementProposition55 (n k : ℕ) : Prop :=
  Proposition55Interface k (symbolicX n) (symbolicParameter n)
def StatementProposition61 (n : ℕ) : Prop :=
  Proposition61Interface (symbolicX n) (symbolicParameter n) (symbolicParameter n)
def StatementCorollary62 (n k : ℕ) : Prop :=
  Corollary62Interface k (symbolicX n)

end Fidelity.Spec
