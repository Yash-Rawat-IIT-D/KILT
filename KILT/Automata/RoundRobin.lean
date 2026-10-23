import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Push

/-! # Round-robin recurrence
Pure proof infrastructure: a bounded counter waits for its current obligation,
then advances, wrapping to zero. No assumptions about graph seriality are used.
-/
namespace KILT.Automata.RoundRobin
open Filter

private theorem stays {c : Nat → Nat} {P : Nat → Nat → Prop}
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    {t i : Nat} (ht : c t = i) (nohit : ∀ k ≥ t, ¬ (c k = i ∧ P k i)) :
    ∀ k ≥ t, c k = i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ht
  | succ k hk ih =>
    rw [stay k (by simpa [ih] using fun h => nohit k hk ⟨ih, h⟩), ih]

private theorem next_hit {c : Nat → Nat} {P : Nat → Nat → Prop}
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    {t i : Nat} (ht : c t = i) (hp : ∃ᶠ k in atTop, P k i) :
    ∃ k ≥ t, c k = i ∧ P k i := by
  by_contra! h
  have hc := stays stay ht (fun k hk hh => h k hk hh.1 hh.2)
  obtain ⟨k, hk, hp⟩ := frequently_atTop.mp hp t
  exact h k hk (hc k hk) hp

/-- Recurrence of every obligation forces recurring completed rounds. -/
theorem complete {n : Nat} (hn : 0 < n) {c : Nat → Nat} {P : Nat → Nat → Prop}
    (bound : ∀ k, c k < n)
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    (move : ∀ k, P k (c k) → c (k+1) = if c k + 1 < n then c k + 1 else 0)
    (freq : ∀ i < n, ∃ᶠ k in atTop, P k i) :
    ∃ᶠ k in atTop, c k = 0 ∧ P k 0 := by
  have reach : ∀ d t, n - c t = d → ∃ k ≥ t, c k = 0 ∧ P k 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro t hd
      obtain ⟨k, hk, he, hp⟩ := next_hit stay rfl (freq (c t) (bound t))
      by_cases hz : c t = 0
      · exact ⟨k, hk, he.trans hz, hz ▸ hp⟩
      have hm := move k (he ▸ hp)
      by_cases hnext : c k + 1 < n
      · rw [ite_eq_left hnext] at hm
        have hlt : n - c (k+1) < d := by have := bound t; omega
        obtain ⟨j, hj, h⟩ := ih _ hlt (k+1) rfl
        exact ⟨j, by omega, h⟩
      · rw [ite_eq_right hnext] at hm
        obtain ⟨j, hj, h⟩ := next_hit stay hm (freq 0 hn)
        exact ⟨j, by omega, h⟩
  exact frequently_atTop.mpr fun t => reach _ t rfl

/-- Recurring completions force each intermediate obligation to be discharged. -/
theorem sound {n : Nat} (_hn : 0 < n) {c : Nat → Nat} {P : Nat → Nat → Prop}
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    (move : ∀ k, P k (c k) → c (k+1) = if c k + 1 < n then c k + 1 else 0)
    (freq : ∃ᶠ k in atTop, c k = 0 ∧ P k 0) :
    ∀ i < n, ∃ᶠ k in atTop, P k i := by
  have hits : ∀ i < n, ∃ᶠ k in atTop, c k = i ∧ P k i := by
    intro i
    induction i with
    | zero => exact fun _ => freq
    | succ i ih =>
      intro hi
      have prev := ih (by omega)
      apply frequently_atTop.mpr
      intro t
      obtain ⟨k, hk, he, hp⟩ := frequently_atTop.mp prev t
      have hm := move k (he ▸ hp)
      rw [ite_eq_left (by omega)] at hm
      have hs : c (k+1) = i+1 := by omega
      have hh : ∃ j ≥ k+1, c j = i+1 ∧ P j (i+1) := by
        by_contra! h
        have hc := stays stay hs (fun j hj hh => h j hj hh.1 hh.2)
        obtain ⟨j, hj, hz, _⟩ := frequently_atTop.mp freq (k+1)
        have := hc j hj
        omega
      obtain ⟨j, hj, hh⟩ := hh
      exact ⟨j, by omega, hh⟩
  exact fun i hi => (hits i hi).mono fun _ h => h.2
end KILT.Automata.RoundRobin
