import AffineDualJT.Basic

/-! # The ordered matrix blocks used in Theorem 3.1. -/

namespace AffineDualJT
open Matrix

section Blocks
variable {F : Type*}

def firstCols {n k : ℕ} (X : Matrix (Fin n) (Fin (n+k)) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => X i ⟨j.1, by omega⟩
def lastRowsY {n k : ℕ} (Y : Matrix (Fin (n+k)) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => Y ⟨k+i.1, by omega⟩ j
def tailRowsAfterN {n k : ℕ} (U : Matrix (Fin (n+k)) (Fin k) F) : Matrix (Fin k) (Fin k) F :=
  fun i j => U ⟨n+i.1, by omega⟩ j
def firstRowsZ {n k : ℕ} (Z : Matrix (Fin (n+k)) (Fin k) F) : Matrix (Fin k) (Fin k) F :=
  fun i j => Z ⟨i.1, by omega⟩ j
end Blocks

end AffineDualJT
