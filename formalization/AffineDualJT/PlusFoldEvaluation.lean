import AffineDualJT.BracketEvaluation
import AffineDualJT.Folding

/-! # Evaluating the normalized center row against `[m]_+` -/
namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {L : ℕ}

/-- The doubled bracket and the normalized center coefficient compensate. -/
theorem bracketPlus_sum_normalized (g : ℤ → F) (href : ∀ m, g (2-m)=g m)
    (c : Fin L → F) (hcenter : ∀ p, p.val=0 → 2*c p=g 1)
    (hpositive : ∀ p, p.val≠0 → c p=g (paperIndex p))
    (m : ℤ) (hlo : 2-(L:ℤ) ≤ m) (hhi : m ≤ (L:ℤ)) :
    (∑ p : Fin L, bracketPlus m p*c p)=g m := by
  classical
  have hpos (a : ℤ) (ha : 1 ≤ a) (hLa : a ≤ (L:ℤ)) :
      (∑ p : Fin L, bracketPlus a p*c p)=g a := by
    obtain ⟨q,rfl⟩ := exists_paperIndex a ha hLa
    simp only [bracketPlus_paperIndex,ite_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,ite_true]
    by_cases hq : q.val=0
    · rw [ite_eq_left hq,show paperIndex q=1 by simp [paperIndex,hq]]
      exact hcenter q hq
    · rw [ite_eq_right hq,one_mul,hpositive q hq]
  by_cases hm : 1 ≤ m
  · exact hpos m hm hhi
  have h := hpos (2-m) (by omega) (by omega)
  simpa only [bracketPlus_reflect,href] using h

end
end AffineDualJT
