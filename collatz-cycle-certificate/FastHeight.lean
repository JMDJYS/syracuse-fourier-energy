import Collatz.TwoRiseCheck

/-! The inverse update used by the paper, evaluated with division by three. -/

namespace Cycle108

open Collatz.TwoRise

def updateInverse (W c : Nat) : Nat :=
  Nat.add (Nat.div c 3) (Nat.mul (Nat.mod c 3) (Nat.div (Nat.add (Nat.pow 2 W) 1) 3))

theorem updateInverse_eq {W c : Nat} (hW : 2 ^ W % 3 = 2) :
    3 * updateInverse W c = c + (c % 3) * 2 ^ W := by
  have h1 := Nat.div_add_mod c 3
  have h2 : 3 * ((2 ^ W + 1) / 3) = 2 ^ W + 1 := by omega
  change 3 * (c / 3 + (c % 3) * ((2 ^ W + 1) / 3)) = _
  rw [Nat.mul_add, Nat.mul_left_comm 3 (c % 3), h2, Nat.mul_add, Nat.mul_one]
  omega

theorem updateInverse_sound {W k c : Nat} (hW : 2 ^ W % 3 = 2)
    (hk : 1 ≤ k) (hc : 3 ^ (k - 1) * c % 2 ^ W = 1) :
    3 ^ k * updateInverse W c % 2 ^ W = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_assoc, updateInverse_eq hW, Nat.mul_add, ← Nat.mul_assoc]
  rw [Nat.add_mul_mod_self_right]
  simpa using hc

theorem updateInverse_lt {W c : Nat} (hW : 2 ^ W % 3 = 2) (hc : c < 2 ^ W) :
    updateInverse W c < 2 ^ W := by
  have he := updateInverse_eq (c := c) hW
  have hm : c % 3 ≤ 2 := by omega
  have hm' := Nat.mul_le_mul_right (2 ^ W) hm
  omega

def fastLoop (N B E W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := updateInverse W c
      kOK N B E W k c' && ih (Nat.add k 1) c') cnt

def rangeCheck (N B E W k c cnt : Nat) : Bool :=
  Nat.ble 1 k && Nat.beq (Nat.mod (Nat.pow 2 W) 3) 2 &&
    Nat.blt c (Nat.pow 2 W) &&
    Nat.beq (Nat.mod (Nat.mul (Nat.pow 3 (Nat.sub k 1)) c) (Nat.pow 2 W)) 1 &&
    fastLoop N B E W cnt k c

private theorem fastLoop_sound {N B E W : Nat} (hW : 2 ^ W % 3 = 2) :
    ∀ cnt k c, 1 ≤ k → c < 2 ^ W → 3 ^ (k - 1) * c % 2 ^ W = 1 →
      fastLoop N B E W cnt k c = true → RangeCond N B k (k + cnt) := by
  intro cnt
  induction cnt with
  | zero => intro k c _ _ _ _ a hlo hhi; omega
  | succ cnt ih =>
    intro k c hk hcLt hc h a hlo hhi ha
    change (kOK N B E W k (updateInverse W c) &&
      fastLoop N B E W cnt (k + 1) (updateInverse W c)) = true at h
    obtain ⟨hfirst, hrest⟩ := Bool.and_eq_true_iff.mp h
    have hi := updateInverse_sound hW hk hc
    have hLt := updateInverse_lt hW hcLt
    by_cases hak : a = k
    · subst hak
      exact kOK_sound hfirst hi hLt ha
    · exact ih (k+1) (updateInverse W c) (by omega) hLt (by simpa using hi)
        hrest a (by omega) (by omega) ha

theorem rangeCheck_sound {N B E W k c cnt : Nat}
    (h : rangeCheck N B E W k c cnt = true) : RangeCond N B k (k + cnt) := by
  simp only [rangeCheck, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hk, hw⟩, hLt⟩, hc⟩, hl⟩ := h
  exact fastLoop_sound hw cnt k c hk hLt hc hl

#print axioms rangeCheck_sound

end Cycle108
