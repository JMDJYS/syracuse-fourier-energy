/-! Lean 4.24 equivalents of core lemmas used by the imported two-rise checker. -/

namespace Int

theorem dvd_mul_of_dvd_right {a b c : Int} (h : a ∣ b) : a ∣ c * b := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨c * d, by grind⟩

end Int

namespace Nat

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem lor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem isPowerOfTwo_of_and_sub_one_eq_zero {n : Nat} (hn : 0 < n)
    (h : n &&& (n - 1) = 0) : n.isPowerOfTwo := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases he : n % 2 = 0
    · let m := n / 2
      have hm : 0 < m := by omega
      have hm' : m < n := by omega
      have hd : (n - 1) / 2 = m - 1 := by omega
      have hd' := congrArg (fun x : Nat => x >>> 1) h
      change (n &&& (n - 1)) >>> 1 = (0 : Nat) >>> 1 at hd'
      rw [Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow] at hd'
      simp only [Nat.pow_one, Nat.zero_shiftRight, hd] at hd'
      obtain ⟨k, hk⟩ := ih m hm' hm hd'
      refine ⟨k + 1, ?_⟩
      have hh : 2 * m = n := by omega
      rw [Nat.pow_succ, ← hk]
      omega
    · let m := n / 2
      have hd : (n - 1) / 2 = m := by omega
      have hd' := congrArg (fun x : Nat => x >>> 1) h
      change (n &&& (n - 1)) >>> 1 = (0 : Nat) >>> 1 at hd'
      rw [Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow] at hd'
      simp only [Nat.pow_one, Nat.zero_shiftRight, hd, ← show m = n / 2 from rfl,
        Nat.and_self] at hd'
      refine ⟨0, ?_⟩
      simp only [Nat.pow_zero]
      omega

end Nat
