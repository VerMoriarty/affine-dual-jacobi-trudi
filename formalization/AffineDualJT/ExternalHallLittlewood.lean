import AffineDualJT.HallLittlewoodWeyl

/-!
# Seven rectangular Hall--Littlewood polynomials

These are the exact seven specializations of source.tex (2.1), with the
boundary and width-zero normalization data in its table. The Weyl orbit
sum is implemented in `HallLittlewoodWeyl.lean`. The symmetrizer reduction
to (2.2) is a separate theorem and is not built into these definitions.
-/

namespace AffineDualJT
noncomputable section

namespace ExternalHL
variable {F : Type*} [Field F]

/-- `P^{C_n}_{(k^n)}(x;t,0)`, Warnaar [7, (2.16)--(2.17)]. -/
noncomputable def C0 {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  weylSum x t k (fun z => (1-z^2)⁻¹) 1
/-- `P^{C_n}_{(k^n)}(x;t,t)`. -/
noncomputable def Ct {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  weylSum x t k (fun z => (1-t*z^2)/(1-z^2)) (nuCt n k t)
/-- `P^{BC_n}_{(k^n)}(x;τ²,-τ,0)`. -/
noncomputable def BC {n : ℕ} (x : Fin n → Fˣ) (τ : F) (k : ℕ) : F :=
  weylSum x (τ^2) k (fun z => (1+τ*z)/(1-z^2)) 1
/-- `P^{B_n}_{(k^n)}(x;t,0)`. -/
noncomputable def B0 {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  weylSum x t k (fun z => (1-z)⁻¹) 1
/-- `P^{B_n}_{(k^n)}(x;τ²,-τ)`. -/
noncomputable def Bminus {n : ℕ} (x : Fin n → Fˣ) (τ : F) (k : ℕ) : F :=
  weylSum x (τ^2) k (fun z => (1+τ*z)/(1-z)) (nuBminus n k τ)
/-- `P^{B_n}_{(k^n)}(x;t,1)`. -/
noncomputable def Bplus {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  weylSum x t k (fun _ => 1) (nuBplus n k t)
/-- `P^{B_n}_{(k^n)}(x;t,t)`. -/
noncomputable def Bt {n : ℕ} (x : Fin n → Fˣ) (t : F) (k : ℕ) : F :=
  weylSum x t k (fun z => (1-t*z)/(1-z)) (nuCt n k t)

end ExternalHL
end
end AffineDualJT
