import FidelityLean.ZeroParameterSpec
import FidelityLean.MainCertificates

noncomputable section
namespace Fidelity.Bridge

theorem matrix_of_eq {m n F : Type*} (f : m → n → F) :
    (Matrix.of f : Matrix m n F) = (fun i j => f i j) := rfl

end Fidelity.Bridge
namespace Fidelity.Certificate
open Fidelity.Bridge

/-- Corollary 6.2, including its seven-case final sentence. -/
theorem zero_specialization (c : Spec.PaperCase) (n k : ℕ) :
    Spec.ZeroSpecialization c n k := by
  intro hn hk
  cases c with
  | C0 =>
    simpa only [P_C0, Spec.caseFolding, Spec.classicalNumerator,
      Delta_C_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_C0_zero (n := n) (k := k) hn hk)
  | Ct =>
    simpa only [P_Ct, Spec.caseFolding, Spec.classicalNumerator,
      Delta_C_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_Ct_zero (n := n) (k := k) hn hk)
  | BC =>
    simpa only [P_BC, Spec.caseFolding, Spec.classicalNumerator,
      Delta_C_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_BC_zero (n := n) (k := k) hn hk)
  | B0 =>
    simpa only [P_B0, Spec.caseFolding, Spec.classicalNumerator,
      Delta_B_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_B0_zero (n := n) (k := k) hn hk)
  | Bminus =>
    simpa only [P_Bminus, Spec.caseFolding, Spec.classicalNumerator,
      Delta_B_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_Bminus_zero (n := n) (k := k) hn hk)
  | Bplus =>
    simpa only [P_Bplus, Spec.caseFolding, Spec.classicalNumerator,
      Delta_plus_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_Bplus_zero (n := n) (k := k) hn hk)
  | Bt =>
    simpa only [P_Bt, Spec.caseFolding, Spec.classicalNumerator,
      Delta_B_eq, Spec.phi, Spec.psi, Spec.cosine,
      AffineDualJT.phi, AffineDualJT.psi, AffineDualJT.Cfun,
      paperIndex_eq, symbolicX_eq, matrix_of_eq] using
        (AffineDualJT.paper_cor_6_2_Bt_zero (n := n) (k := k) hn hk)

theorem corollary_6_2_zero (n k : ℕ) : Spec.Corollary62ZeroSpecializations n k := by
  intro c
  exact zero_specialization c n k

end Fidelity.Certificate
