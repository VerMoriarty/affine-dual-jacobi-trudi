import FidelityLean.Spec

/-!
Independent addendum for authoritative.pdf, Corollary 6.2, p. 14, final
sentence; its proof begins on p. 15. The seven original Weyl objects at
t = 0 (and tau = 0 in the two square-root cases) equal the corresponding
finite classical ratios on the left of (6.1), (6.2), and (6.3).

These are proposition interfaces only. No paper result is proved or assumed.
The frozen Spec.lean and paper_a files are unchanged. In particular, the
one-half factors on the right of (6.2)/(6.3) are not inserted into their
left-hand finite ratios.
-/

namespace Fidelity.Spec

/-- Corollary 6.2's seven zero-parameter specializations, with precisely its
positive-rank and positive-width assumptions. -/
def ZeroSpecialization (c : PaperCase) (n k : ℕ) : Prop :=
  0 < n → 0 < k →
    P c k (symbolicX n) (0 : ParameterField n) 0 =
      classicalNumerator (caseFolding c) k (symbolicX n) /
        Delta (caseFolding c) (symbolicX n)

def ZeroSpecializationC0 (n k : ℕ) : Prop := ZeroSpecialization .C0 n k
def ZeroSpecializationCt (n k : ℕ) : Prop := ZeroSpecialization .Ct n k
def ZeroSpecializationBC (n k : ℕ) : Prop := ZeroSpecialization .BC n k
def ZeroSpecializationB0 (n k : ℕ) : Prop := ZeroSpecialization .B0 n k
def ZeroSpecializationBminus (n k : ℕ) : Prop := ZeroSpecialization .Bminus n k
def ZeroSpecializationBplus (n k : ℕ) : Prop := ZeroSpecialization .Bplus n k
def ZeroSpecializationBt (n k : ℕ) : Prop := ZeroSpecialization .Bt n k

/-- An enumerable uniform interface covering all seven cases. -/
def Corollary62ZeroSpecializations (n k : ℕ) : Prop :=
  ∀ c : PaperCase, ZeroSpecialization c n k

end Fidelity.Spec
