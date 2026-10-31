import AffineDualJT.MatrixBlocks

/-!
# Signs of the block permutations used in the complementary-minor argument

The block flip exchanges an initial block of size `n` with a final block of
size `k`. Its sign is `(-1)^(n*k)`, since each of the `n` entries crosses the
`k` entries in the other block.
-/

namespace AffineDualJT

def paperBlockFlip (n k : ℕ) : Equiv.Perm (Fin (n+k)) :=
  finAddFlip.trans (finCongr (Nat.add_comm k n))

theorem paperBlockFlip_zero (k : ℕ) : paperBlockFlip 0 k = 1 := by
  ext i
  obtain ⟨a, rfl⟩ := (finSumFinEquiv (m:=0) (n:=k)).surjective i
  cases a with
  | inl a => exact a.elim0
  | inr b =>
    simp only [paperBlockFlip, Equiv.trans_apply, finSumFinEquiv_apply_right,
      finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
      Fin.val_natAdd, Equiv.Perm.one_apply]
    omega

theorem paperBlockFlip_pow (n k : ℕ) (hn : 0 < n) :
    paperBlockFlip n k = (finRotate (n+k)) ^ k := by
  let : NeZero (n+k) := ⟨by omega⟩
  let s : Fin (n+k) := ⟨k, by omega⟩
  have hp : paperBlockFlip n k = finCycle s := by
    ext i
    obtain ⟨a, rfl⟩ := (finSumFinEquiv (m:=n) (n:=k)).surjective i
    cases a with
    | inl a =>
      simp only [paperBlockFlip, Equiv.trans_apply, finSumFinEquiv_apply_left,
        finAddFlip_apply_castAdd, finCongr_apply, Fin.val_cast, Fin.val_natAdd,
        finCycle_apply, Fin.val_add, Fin.val_castAdd]
      change k + a.val = (a.val + k) % (n+k)
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    | inr b =>
      simp only [paperBlockFlip, Equiv.trans_apply, finSumFinEquiv_apply_right,
        finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast, Fin.val_castAdd,
        finCycle_apply, Fin.val_add, Fin.val_natAdd]
      change b.val = (n + b.val + k) % (n+k)
      rw [show n + b.val + k = n + k + b.val by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
  rw [hp]
  ext i
  exact congrArg Fin.val (by
    simpa only [Equiv.Perm.coe_pow, s] using congrFun (finCycle_eq_finRotate_iterate (k:=s)) i)

theorem paperBlockFlip_sign (n k : ℕ) :
    Equiv.Perm.sign (paperBlockFlip n k) = (-1) ^ (n*k) := by
  by_cases hn : n = 0
  · subst n
    rw [paperBlockFlip_zero]
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [paperBlockFlip_pow n k hnpos, map_pow, sign_finRotate, ← pow_mul]
  by_cases hk : k = 0
  · subst k
    simp
  have hsub : n + k - 1 = n + (k - 1) := by omega
  have he : (n+k-1)*k = n*k + k*(k-1) := by rw [hsub]; ring
  rw [he, pow_add, (Nat.even_mul_pred_self k).neg_one_pow, mul_one]

end AffineDualJT
