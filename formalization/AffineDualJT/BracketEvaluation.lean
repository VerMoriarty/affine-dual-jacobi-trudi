import AffineDualJT.FiniteColumnData

/-!
# Finite bracket evaluation, source.tex §2.1--2.2

The bounds state exactly when the folded index lies among the available
rows. In particular `[1]_+=2e₁` is retained.
-/

namespace AffineDualJT
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] {L : ℕ}

theorem paperIndex_injective : Function.Injective (paperIndex (k := L)) := by
  intro p q h
  apply Fin.ext
  simp only [paperIndex] at h
  omega

theorem exists_paperIndex (m : ℤ) (hm : 1 ≤ m) (hL : m ≤ (L:ℤ)) :
    ∃ p : Fin L, paperIndex p = m := by
  refine ⟨⟨(m-1).toNat, by omega⟩, ?_⟩
  simp only [paperIndex]
  omega

theorem bracketC_paperIndex (p q : Fin L) :
    bracketC (F := F) (paperIndex p) q = if p=q then 1 else 0 := by
  have he : paperIndex p = paperIndex q ↔ p=q := ⟨fun h => paperIndex_injective h, congrArg paperIndex⟩
  have hp := paperIndex_pos p
  have hq := paperIndex_pos q
  simp only [bracketC, he, show paperIndex p ≠ -paperIndex q by omega, ite_false]

theorem bracketB_paperIndex (p q : Fin L) :
    bracketB (F := F) (paperIndex p) q = if p=q then 1 else 0 := by
  have he : paperIndex p = paperIndex q ↔ p=q := ⟨fun h => paperIndex_injective h, congrArg paperIndex⟩
  have hp := paperIndex_pos p
  have hq := paperIndex_pos q
  simp only [bracketB, he, show 1-paperIndex p ≠ paperIndex q by omega, ite_false]

theorem bracketPlus_paperIndex (p q : Fin L) :
    bracketPlus (F := F) (paperIndex p) q =
      if p=q then (if p.val=0 then 2 else 1) else 0 := by
  have he : paperIndex p = paperIndex q ↔ p=q := ⟨fun h => paperIndex_injective h, congrArg paperIndex⟩
  have hp := paperIndex_pos p
  have hq := paperIndex_pos q
  by_cases hp0 : p.val=0
  · have hp1 : paperIndex p=1 := by simp [paperIndex,hp0]
    have hqp : q.val=0 ↔ p=q := by
      constructor
      · intro h; apply Fin.ext; omega
      · intro h; rw [← h,hp0]
    simp only [bracketPlus,hp1,hqp,hp0,ite_true]
  · have hp1 : paperIndex p≠1 := by simp only [paperIndex]; omega
    have href : 2-paperIndex p ≠ paperIndex q := by simp only [paperIndex] at *; omega
    simp only [bracketPlus,hp1,he,href,hp0,ite_false]

theorem bracketC_neg (m : ℤ) (p : Fin L) :
    bracketC (F := F) (-m) p = -bracketC m p := by
  have hp := paperIndex_pos p
  simp only [bracketC]
  split_ifs <;> try norm_num <;> omega

theorem bracketB_reflect (m : ℤ) (p : Fin L) :
    bracketB (F := F) (1-m) p = -bracketB m p := by
  have hp := paperIndex_pos p
  simp only [bracketB]
  split_ifs <;> try norm_num <;> omega

theorem bracketPlus_reflect (m : ℤ) (p : Fin L) :
    bracketPlus (F := F) (2-m) p = bracketPlus m p := by
  have hp := paperIndex_pos p
  simp only [bracketPlus]
  split_ifs <;> (first | rfl | omega)

private theorem bracketC_sum_positive (g : ℤ → F) (m : ℤ)
    (hm : 1 ≤ m) (hL : m ≤ (L:ℤ)) :
    (∑ p : Fin L, bracketC m p*g (paperIndex p)) = g m := by
  classical
  obtain ⟨q,rfl⟩ := exists_paperIndex m hm hL
  simp only [bracketC_paperIndex,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

private theorem bracketB_sum_positive (g : ℤ → F) (m : ℤ)
    (hm : 1 ≤ m) (hL : m ≤ (L:ℤ)) :
    (∑ p : Fin L, bracketB m p*g (paperIndex p)) = g m := by
  classical
  obtain ⟨q,rfl⟩ := exists_paperIndex m hm hL
  simp only [bracketB_paperIndex,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

/-- Evaluation against the odd folding, including its omitted zero index. -/
theorem bracketC_sum (g : ℤ → F) (hneg : ∀ m, g (-m) = -g m) (hzero : g 0=0)
    (m : ℤ) (hlo : -(L:ℤ) ≤ m) (hhi : m ≤ (L:ℤ)) :
    (∑ p : Fin L, bracketC m p*g (paperIndex p)) = g m := by
  by_cases hm : 0 < m
  · exact bracketC_sum_positive g m (by omega) hhi
  by_cases hm0 : m=0
  · subst m
    have hb (p : Fin L) : bracketC (F := F) 0 p=0 := by
      have hp := paperIndex_pos p
      simp only [bracketC,show (0:ℤ)≠paperIndex p by omega,show (0:ℤ)≠-paperIndex p by omega,ite_false]
    simp only [hb,hzero,zero_mul,Finset.sum_const_zero]
  have h := bracketC_sum_positive g (-m) (by omega) (by omega : -m ≤ (L:ℤ))
  simp only [bracketC_neg,neg_mul,Finset.sum_neg_distrib,hneg] at h
  exact neg_injective h

/-- Evaluation against the `1-m` folding. -/
theorem bracketB_sum (g : ℤ → F) (href : ∀ m, g (1-m) = -g m)
    (m : ℤ) (hlo : 1-(L:ℤ) ≤ m) (hhi : m ≤ (L:ℤ)) :
    (∑ p : Fin L, bracketB m p*g (paperIndex p)) = g m := by
  by_cases hm : 0 < m
  · exact bracketB_sum_positive g m (by omega) hhi
  have h := bracketB_sum_positive g (1-m) (by omega) (by omega : 1-m ≤ (L:ℤ))
  simp only [bracketB_reflect,neg_mul,Finset.sum_neg_distrib,href] at h
  exact neg_injective h

theorem phi_neg (z : F) (m : ℤ) : phi (-m) z = -phi m z := by
  simp [phi]

theorem psi_reflect (z : F) (m : ℤ) : psi (1-m) z = -psi m z := by
  simp [psi,show 1-(1-m)=m by ring]

theorem Cfun_neg (z : F) (m : ℤ) : Cfun (-m) z = Cfun m z := by
  simp [Cfun,add_comm]

/-- `Φ^C[m]_C=φ_m(x)`, with the available-row bounds from §2.1. -/
theorem PhiC_bracket {n k : ℕ} (x : Fin n → Fˣ) (a : Fin n) (m : ℤ)
    (hlo : -((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
    (∑ p : Fin (n+k), PhiC x a p * bracketC m p) = phi m (x a : F) := by
  simpa only [PhiC,mul_comm] using
    bracketC_sum (fun m => phi m (x a : F)) (phi_neg _) (by simp [phi]) m hlo hhi

/-- `Φ^B[m]_B=ψ_m(x)`. -/
theorem PhiB_bracket {n k : ℕ} (x : Fin n → Fˣ) (a : Fin n) (m : ℤ)
    (hlo : 1-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
    (∑ p : Fin (n+k), PhiB x a p * bracketB m p) = psi m (x a : F) := by
  simpa only [PhiB,mul_comm] using
    bracketB_sum (fun m => psi m (x a : F)) (psi_reflect _) m hlo hhi

/-- `Φ^+[m]_+=C_{m-1}(x)`, including `[1]_+=2e₁`. -/
theorem PhiPlus_bracket {n k : ℕ} (x : Fin n → Fˣ) (a : Fin n) (m : ℤ)
    (hlo : 2-((n+k:ℕ):ℤ) ≤ m) (hhi : m ≤ ((n+k:ℕ):ℤ)) :
    (∑ p : Fin (n+k), PhiPlus x a p * bracketPlus m p) = Cfun (m-1) (x a : F) := by
  classical
  have hpos (b : ℤ) (hb : 1 ≤ b) (hLb : b ≤ ((n+k:ℕ):ℤ)) :
      (∑ p : Fin (n+k), PhiPlus x a p * bracketPlus b p) = Cfun (b-1) (x a : F) := by
    obtain ⟨q,rfl⟩ := exists_paperIndex b hb hLb
    simp only [PhiPlus,bracketPlus_paperIndex,mul_ite,mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true,paperIndex,add_sub_cancel_right]
    by_cases hq : q.val=0
    · norm_num [hq,Cfun]
    · simp [hq]
  by_cases hm : 1 ≤ m
  · exact hpos m hm hhi
  have h := hpos (2-m) (by omega) (by omega)
  rw [show 2-m-1= -(m-1) by ring,Cfun_neg] at h
  simpa only [bracketPlus_reflect] using h

end
end AffineDualJT
