import FastHeight
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-! A reduction of the expensive product in the direct check. -/

namespace Cycle108

open Collatz.TwoRise

def reducedResidue (D c L : Nat) : Nat :=
  let J := Nat.mul D L
  Nat.mod (Nat.sub (Nat.add (Nat.mod c J) J) (Nat.mul (Nat.mod c D) L)) J

theorem reducedResidue_eq (D c L : Nat) (hD : 0 < D) :
    reducedResidue D c L = c * (D*L+1-L) % (D*L) := by
  let J := D*L
  let q := (c%D)*L
  let R := c%J+J-q
  have hL : L ≤ J := by
    dsimp [J]
    simpa using Nat.mul_le_mul_right L (show 1 ≤ D by omega)
  have hqJ : q ≤ J := by
    exact Nat.mul_le_mul_right L (Nat.mod_lt c hD).le
  have hQR : q ≤ c % J + J := by omega
  have hq : q ≡ c*L [MOD J] := (Nat.mod_modEq c D).mul_right' L
  have hC : c*(J+1-L)+c*L = c*(J+1) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : L ≤ J+1)]
  have hmodC : c*(J+1) ≡ c [MOD J] := by
    apply Nat.modEq_of_dvd
    push_cast
    exact ⟨-(c:Int), by ring⟩
  have hleft : c*(J+1-L) + q ≡ c [MOD J] := by
    apply ((Nat.ModEq.refl (c*(J+1-L))).add hq).trans
    rwa [hC]
  have hright : R+q ≡ c [MOD J] := by
    show c % J + J - q + q ≡ c [MOD J]
    rw [Nat.sub_add_cancel hQR]
    have h : c % J + J ≡ c % J [MOD J] := by
      unfold Nat.ModEq
      simp
    exact h.trans (Nat.mod_modEq c J)
  exact (Nat.ModEq.add_right_cancel' q (hleft.trans hright.symm)).symm

def reducedDirectOK (D A2 W2 c L : Nat) : Bool :=
  if D = 0 then directOK D A2 W2 c L else
    Nat.ble (Nat.mul D L) W2 && Nat.ble A2 (reducedResidue D c L)

theorem reducedDirectOK_eq (D A2 W2 c L : Nat) :
    reducedDirectOK D A2 W2 c L = directOK D A2 W2 c L := by
  unfold reducedDirectOK
  split
  · rfl
  · rw [reducedResidue_eq _ _ _ (by omega)]
    rfl

#print axioms reducedDirectOK_eq

end Cycle108
