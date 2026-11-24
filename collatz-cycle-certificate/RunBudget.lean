import Algebra
import Mathlib.Data.Finset.Card

/-! A one-pass form of the low-return budget for a sequence started at a low
minimum. Each run is charged according to its distance from the last low
minimum. This avoids choosing a cyclic partition explicitly. -/

namespace Cycle108

open Finset
open scoped BigOperators

def highCount (low : ℕ → Bool) (n : ℕ) : ℕ :=
  ((range n).filter (fun i => low i = false)).card

theorem highCount_le (low : ℕ → Bool) (n : ℕ) : highCount low n ≤ n := by
  simpa [highCount] using card_filter_le (s := range n) (p := fun i => low i = false)

theorem highCount_succ (low : ℕ → Bool) (n : ℕ) :
    highCount low (n+1) = highCount low n + if low n then 0 else 1 := by
  unfold highCount
  rw [range_add_one, filter_insert]
  cases h : low n <;> simp [h]

def streak (low : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if low (n+1) then 0 else streak low n + 1

theorem streak_origin {low : ℕ → Bool} (h0 : low 0 = true) (n : ℕ) :
    streak low n ≤ n ∧ low (n - streak low n) = true := by
  induction n with
  | zero => simpa [streak] using h0
  | succ n ih =>
    cases h : low (n+1) with
    | true => simp [streak, h]
    | false =>
      simp only [streak, h, Bool.false_eq_true, if_false]
      have e : n+1-(streak low n+1) = n-streak low n := by omega
      exact ⟨by omega, e ▸ ih.2⟩

theorem streak_high (low : ℕ → Bool) (n : ℕ) :
    streak low n ≤ highCount low (n+1) := by
  induction n with
  | zero => simp [streak]
  | succ n ih =>
    rw [streak, highCount_succ low (n+1)]
    cases h : low (n+1) <;> simp_all

theorem streak_zero {low : ℕ → Bool} {n : ℕ} (h : low n = true) :
    streak low n = 0 := by
  cases n <;> simp_all [streak]

theorem reset_budget {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {low : ℕ → Bool} (h0 : low 0 = true) {a w : ℕ → R} (hmono : Monotone w)
    (hbound : ∀ i, low i = true → ∀ d, a (i + d) ≤ w d) (n : ℕ) :
    budget a n ≤ (n-highCount low n) • w 0 +
      budget (fun i => w (i+1)) (highCount low n) := by
  have ha : ∀ i, a i ≤ w (streak low i) := by
    intro i
    obtain ⟨hle, hlo⟩ := streak_origin h0 i
    simpa only [Nat.sub_add_cancel hle] using hbound _ hlo (streak low i)
  induction n with
  | zero => simp [budget, highCount]
  | succ n ih =>
    have e : budget a (n+1) = budget a n + a n := sum_range_succ _ _
    rw [e, highCount_succ]
    have hc := highCount_le low n
    cases h : low n with
    | true =>
      simp only [if_true, Nat.add_zero]
      have e : n+1-highCount low n = n-highCount low n+1 := by omega
      rw [e, succ_nsmul]
      have ha' := (streak_zero h) ▸ ha n
      simpa only [add_assoc, add_left_comm, add_comm] using add_le_add ih ha'
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have e : n+1-(highCount low n+1) = n-highCount low n := by omega
      have e' : budget (fun i => w (i+1)) (highCount low n+1) =
          budget (fun i => w (i+1)) (highCount low n) + w (highCount low n+1) :=
        sum_range_succ _ _
      rw [e, e']
      have he : highCount low (n+1) = highCount low n+1 := by simp [highCount_succ, h]
      have ha' := (ha n).trans (hmono ((he ▸ streak_high low n)))
      simpa only [add_assoc, add_left_comm, add_comm] using add_le_add ih ha'

#print axioms reset_budget

end Cycle108
