import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Push

/-! # Round-robin recurrence

This module proves the recurrence argument behind the standard round-robin
reduction from a finite family of generalized Büchi obligations to one Büchi
round-completion condition. The argument is abstracted from automata states and
uses only:

* `c k`: the index of the obligation selected by the counter at position `k`;
* `P k i`: the proposition that obligation `i` holds at position `k`.

A hit of `i` is a position where both `c k = i` and `P k i`: occurrences while
the counter is waiting for another obligation do not advance it.

`stays` shows that a counter with no future hit remains stuck, and `next_hit`
combines this fact with infinite recurrence to obtain a future selected hit.
`complete` repeatedly uses that progress to turn recurrence of every obligation
into recurring completed rounds;

`sound` proves the converse by showing that a
recurring completion must repeatedly pass through every intermediate
obligation. `GeneralizedBuchiCorrect` instantiates the two directions to prove
that KILT's round-robin conversion preserves the accepted LTL word language.
-/
namespace KILT.Automata.RoundRobin
open Filter

/-- If the counter is at `i` at time `t` and has no later hit of `i`—no position
where it is still selecting `i` while `P` holds for `i`—then the `stay` rule
keeps it at `i` forever. -/
private theorem stays {c : Nat → Nat} {P : Nat → Nat → Prop}
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    {t i : Nat} (ht : c t = i) (nohit : ∀ k ≥ t, ¬ (c k = i ∧ P k i)) :
    ∀ k ≥ t, c k = i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ht
  | succ k hk ih =>
    rw [stay k (by simpa [ih] using fun h => nohit k hk ⟨ih, h⟩), ih]

/-- A hit of `i` is a position where the counter selects `i` and `P` holds for
`i` simultaneously. If the counter is waiting at `i` and `P` holds for `i`
infinitely often, such a selected hit must eventually occur. -/
private theorem next_hit {c : Nat → Nat} {P : Nat → Nat → Prop}
    (stay : ∀ k, ¬ P k (c k) → c (k+1) = c k)
    {t i : Nat} (ht : c t = i) (hp : ∃ᶠ k in atTop, P k i) :
    ∃ k ≥ t, c k = i ∧ P k i := by
  by_contra! h
  have hc := stays stay ht (fun k hk hh => h k hk hh.1 hh.2)
  obtain ⟨k, hk, hp⟩ := frequently_atTop.mp hp t
  exact h k hk (hc k hk) hp

/-- If every one of the `n` obligations recurs infinitely often, a bounded
counter that waits for a selected hit and then advances cyclically completes
infinitely many rounds, witnessed by recurring selected hits of obligation
zero. This is the completeness direction of the round-robin reduction. -/
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

/-- If selected hits of obligation zero recur infinitely often, a counter that
can reach the next round only by advancing through the intervening obligations
must discharge every obligation infinitely often. This is the soundness
direction of the round-robin reduction. -/
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
