import AffineDualJT.FiniteWeyl

/-! # Finite brackets, Table 1, and the reduced Weyl sum, source.tex §2.2 -/
namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Brackets
variable {F : Type*} [Field F]
variable {L : ℕ}

/-- `[m]_C`, p.4.  Values outside the available `L` rows are automatically zero. -/
def bracketC (m : ℤ) : Fin L → F := fun p =>
  if m = paperIndex p then 1 else if m = - paperIndex p then -1 else 0

/-- `[m]_B`, p.4. -/
def bracketB (m : ℤ) : Fin L → F := fun p =>
  if m = paperIndex p then 1 else if 1 - m = paperIndex p then -1 else 0

/-- `[m]_+`, p.4; `[1]_+=2e₁`. -/
def bracketPlus (m : ℤ) : Fin L → F := fun p =>
  if m = 1 then (if p.1 = 0 then 2 else 0)
  else if m = paperIndex p then 1
  else if 2 - m = paperIndex p then 1 else 0

end Brackets

section Columns
variable {F : Type*} [Field F]
variable {n k : ℕ}

private def kZ : ℤ := (k : ℤ)

/-- `u^C_r`, p.5, with Lean column `r` corresponding to paper `r+1`. -/
def uC (t : F) (r : Fin n) : Fin (n+k) → F :=
  if r.1 = 0 then bracketC (F:=F) (L:=n+k) ((k : ℤ)+1)
  else fun p => bracketC (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r) p +
    t ^ r.1 * bracketC (F:=F) (L:=n+k) ((k : ℤ)+2-paperIndex r) p

/-- `ũ^C_r`, p.5. -/
def uCTilde (t : F) (r : Fin n) : Fin (n+k) → F :=
  if r.1 = 0 then bracketC (F:=F) (L:=n+k) (k : ℤ)
  else fun p => bracketC (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r-1) p +
    t ^ r.1 * bracketC (F:=F) (L:=n+k) ((k : ℤ)+1-paperIndex r) p

/-- `u^B_r`, p.5. -/
def uB (t : F) (r : Fin n) : Fin (n+k) → F :=
  if r.1 = 0 then bracketB (F:=F) (L:=n+k) ((k : ℤ)+1)
  else fun p => bracketB (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r) p +
    t ^ r.1 * bracketB (F:=F) (L:=n+k) ((k : ℤ)+2-paperIndex r) p

/-- `ũ^B_r`, p.5. -/
def uBTilde (t : F) (r : Fin n) : Fin (n+k) → F :=
  if r.1 = 0 then bracketB (F:=F) (L:=n+k) (k : ℤ)
  else fun p => bracketB (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r-1) p +
    t ^ r.1 * bracketB (F:=F) (L:=n+k) ((k : ℤ)+1-paperIndex r) p

/-- `u^+_r`, p.5. -/
def uPlus (t : F) (r : Fin n) : Fin (n+k) → F :=
  if r.1 = 0 then bracketPlus (F:=F) (L:=n+k) ((k : ℤ)+1)
  else fun p => bracketPlus (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r) p +
    t ^ r.1 * bracketPlus (F:=F) (L:=n+k) ((k : ℤ)+2-paperIndex r) p

/-- Table 1, case `C0`. -/
def VC0 (t : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r => uC (n:=n) (k:=k) t r p
/-- Table 1, case `Ct`. -/
def VCt (t : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r =>
  bracketC (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r) p -
    t ^ (r.1+1) * bracketC (F:=F) (L:=n+k) ((k : ℤ)-paperIndex r) p
/-- Table 1, case `BC`, with `t=τ²`. -/
def VBC (τ : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r =>
  uC (n:=n) (k:=k) (τ^2) r p + τ * uCTilde (n:=n) (k:=k) (τ^2) r p
/-- Table 1, case `B0`. -/
def VB0 (t : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r => uB (n:=n) (k:=k) t r p
/-- Table 1, case `B-`, with `t=τ²`. -/
def VBminus (τ : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r =>
  bracketB (F:=F) (L:=n+k) ((k : ℤ)+paperIndex r) p +
    τ ^ (2*r.1+1) * bracketB (F:=F) (L:=n+k) ((k : ℤ)+1-paperIndex r) p
/-- Table 1, case `B+`. -/
def VBplus (t : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r => uPlus (n:=n) (k:=k) t r p
/-- Table 1, case `Bt`. -/
def VBt (t : F) : Matrix (Fin (n+k)) (Fin n) F := fun p r =>
  uB (n:=n) (k:=k) t r p - t * uBTilde (n:=n) (k:=k) t r p

end Columns

section Reduced
variable {F : Type*} [Field F]

/-- Paper p.3, equation (2.2), abstract reduced Weyl sum for positive width. -/
noncomputable def reducedWeyl {n : ℕ}
    (x : Fin n → Fˣ) (t : F) (k : ℕ) (rho : F → F) : F :=
  ∑ η : Fin n → Bool,
    (∏ a : Fin n,
      (((if η a = true then (x a : F)⁻¹ else (x a : F))⁻¹) ^ k) *
        rho (if η a = true then (x a : F)⁻¹ else (x a : F))) *
    (∏ a : Fin n, ∏ b : {b : Fin n // a < b.1},
      (1 - t * (if η a = true then (x a : F)⁻¹ else (x a : F)) *
        (if η b.1 = true then (x b.1 : F)⁻¹ else (x b.1 : F))) /
      (1 - (if η a = true then (x a : F)⁻¹ else (x a : F)) *
        (if η b.1 = true then (x b.1 : F)⁻¹ else (x b.1 : F))))

noncomputable def RedC0 {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  reducedWeyl x t k (fun z => (1-z^2)⁻¹)
noncomputable def RedCt {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  reducedWeyl x t k (fun z => (1-t*z^2)/(1-z^2))
noncomputable def RedBC {n : ℕ} (x : Fin n → Fˣ) (τ : F) (k : ℕ) : F :=
  reducedWeyl x (τ^2) k (fun z => (1+τ*z)/(1-z^2))
noncomputable def RedB0 {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  reducedWeyl x t k (fun z => (1-z)⁻¹)
noncomputable def RedBminus {n : ℕ} (x : Fin n → Fˣ) (τ : F) (k : ℕ) : F :=
  reducedWeyl x (τ^2) k (fun z => (1+τ*z)/(1-z))
noncomputable def RedBplus {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  reducedWeyl x t k (fun _ => 1)
noncomputable def RedBt {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  reducedWeyl x t k (fun z => (1-t*z)/(1-z))

end Reduced

end
end AffineDualJT
