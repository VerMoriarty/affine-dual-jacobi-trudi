import AffineDualJT.Basic

/-! # The finite Weyl matrices and products, source.tex §2.1 -/

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

/-- `φ_m(z)=z^m-z^{-m}`. -/
def phi (m : ℤ) (z : F) : F := z ^ m - z ^ (-m)
/-- `ψ_m(z)=z^m-z^{1-m}`. -/
def psi (m : ℤ) (z : F) : F := z ^ m - z ^ (1 - m)
/-- `C_m(z)=z^m+z^{-m}`. -/
def Cfun (m : ℤ) (z : F) : F := z ^ m + z ^ (-m)

/-- `N_t(z)=∏_{a<b}(z_a-z_b)(1-t z_a z_b)`. -/
def Nt {R : Type*} [CommRing R] {n : ℕ} (t : R) (z : Fin n → R) : R :=
  ∏ a : Fin n, ∏ b : {b : Fin n // a < b.1},
    (z a - z b.1) * (1 - t * z a * z b.1)

/-- `Φ^C` on pp.4--5. -/
def PhiC {n k : ℕ} (x : Fin n → Fˣ) : Matrix (Fin n) (Fin (n+k)) F :=
  fun a p => phi (paperIndex p) (x a : F)
/-- `Φ^B` on pp.4--5. -/
def PhiB {n k : ℕ} (x : Fin n → Fˣ) : Matrix (Fin n) (Fin (n+k)) F :=
  fun a p => psi (paperIndex p) (x a : F)
/-- `Φ^+` on pp.4--5. -/
def PhiPlus {n k : ℕ} (x : Fin n → Fˣ) : Matrix (Fin n) (Fin (n+k)) F :=
  fun a p => if p.1 = 0 then 1 else Cfun (p.1 : ℤ) (x a : F)

/-- `Δ_C`, equation (2.6). -/
def DeltaC {n : ℕ} (x : Fin n → Fˣ) : F :=
  Matrix.det (fun a r => phi (paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F)
/-- `Δ_B`, equation (2.6). -/
def DeltaB {n : ℕ} (x : Fin n → Fˣ) : F :=
  Matrix.det (fun a r => psi (paperIndex r) (x a : F) : Matrix (Fin n) (Fin n) F)
/-- `Δ_+`, equation (2.6). -/
def DeltaPlus {n : ℕ} (x : Fin n → Fˣ) : F :=
  Matrix.det (fun a r => if r.1 = 0 then 1 else Cfun (r.1 : ℤ) (x a : F) :
    Matrix (Fin n) (Fin n) F)

end
end AffineDualJT
