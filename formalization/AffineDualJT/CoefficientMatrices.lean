import AffineDualJT.MatrixBlocks

/-! # The signed coefficient matrices and normalization signs in §3.2. -/

namespace AffineDualJT
open scoped BigOperators
open Matrix
noncomputable section

section Definitions
variable {F : Type*} [Field F]
variable {n k : ℕ}

def rowSign (p : Fin (n+k)) : F := (-1:F)^(p.1+1)

theorem rowSign_eq_zpow (p : Fin (n+k)) : rowSign (F := F) p = (-1:F)^(paperIndex p) := by
  rw [show paperIndex p = ((p.val+1:ℕ):ℤ) by simp [paperIndex], zpow_natCast]
  rfl

def DC (c : CoeffSystem F n) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p i => rowSign p * lambdaKernel c i (paperIndex p)
def DB (c : CoeffSystem F n) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p i => rowSign p * hKernel c i (paperIndex p)
def DPlus (c : CoeffSystem F n) : Matrix (Fin (n+k)) (Fin k) F :=
  fun p i => rowSign p * hPlusKernel c i (paperIndex p)

def omegaSign (F : Type*) [Field F] (k : ℕ) : F := (-1:F)^(k*(k+1)/2)
def zetaSign (F : Type*) [Field F] (n k : ℕ) : F := (-1:F)^(n*k) * omegaSign F k
end Definitions

end
end AffineDualJT
