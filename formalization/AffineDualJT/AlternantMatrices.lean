import AffineDualJT.WeylMatrices

/-! # The three polynomial alternant matrices of Lemma 2.1 -/

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- `f_r`, with zero-based Lean columns, including the exceptional `f₁`. -/
def fColumn {n : ℕ} (t : R) (r : Fin n) (z : R) : R :=
  if r.val = 0 then z^(n-1)
  else z^(n-(r.val+1)) + t^r.val*z^(n+r.val-1)

def ctAlternantColumn {n : ℕ} (t : R) (r : Fin n) (z : R) : R :=
  z^(n-(r.val+1)) - t^(r.val+1)*z^(n+r.val+1)

def bminusAlternantColumn {n : ℕ} (τ : R) (r : Fin n) (z : R) : R :=
  z^(n-(r.val+1)) + τ^(2*r.val+1)*z^(n+r.val)

theorem map_fColumn {n : ℕ} (f : R →+* S) (t : R) (r : Fin n) (z : R) :
    f (fColumn t r z) = fColumn (f t) r (f z) := by
  classical
  simp [fColumn, apply_ite f]

theorem map_ctAlternantColumn {n : ℕ} (f : R →+* S) (t : R) (r : Fin n) (z : R) :
    f (ctAlternantColumn t r z) = ctAlternantColumn (f t) r (f z) := by
  simp [ctAlternantColumn]

theorem map_bminusAlternantColumn {n : ℕ} (f : R →+* S) (τ : R) (r : Fin n) (z : R) :
    f (bminusAlternantColumn τ r z) = bminusAlternantColumn (f τ) r (f z) := by
  simp [bminusAlternantColumn]

theorem map_Nt {n : ℕ} (f : R →+* S) (t : R) (z : Fin n → R) :
    f (Nt t z) = Nt (f t) (fun a => f (z a)) := by
  simp [Nt]

end
end AffineDualJT
