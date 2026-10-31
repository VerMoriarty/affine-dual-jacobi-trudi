import FidelityLean.MainCertificates
noncomputable section
open Fidelity.Spec
namespace PublicationExample
variable {F : Type*} [Field F]

def MainA13 {n : Nat} (k : Nat)
    (x : Fin n -> Units F) (t : F) : Prop :=
  P .B0 k x t 0 =
    JK (k := k) (2 * (k : Int) + 1)
      (weightB0 t) (hKernel x)

def StatementA13 (n k : Nat) : Prop :=
  0 < n -> MainA13 k (symbolicX n) (symbolicParameter n)

example (n k : Nat) : StatementA13 n k :=
  Fidelity.Certificate.A13 n k
end PublicationExample
