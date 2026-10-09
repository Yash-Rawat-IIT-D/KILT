import KILT.LTL.Semantics

/-!
# Word-semantics examples

Checked examples for the Section 1 semantics. Constant and alternating words
exercise the constructor clauses, derived connectives, and the current/next
position boundary. The temporal examples use explicit proofs and witnesses;
they do not assume decidability of infinite-word satisfaction.
-/

namespace Examples.Words

open KILT.LTL

def atom : Formula Unit := .atom ()

def always : Word Unit := Cslib.ωSequence.const (fun _ => true)
def never : Word Unit := Cslib.ωSequence.const (fun _ => false)
def alternating : Word Unit := ⟨fun i _ => i % 2 == 0⟩

example : ¬ WordSat always .falsehood := by
  intro h
  exact h

example : WordSat always atom := rfl
example : WordSat never (.neg atom) := by
  intro h
  cases h
example : WordSat never (.disj atom (.neg atom)) := Or.inr (by intro h; cases h)
example : WordSat never Formula.truth := fun h => h
example : WordSat alternating atom := rfl
example : ¬ WordSat alternating (.next atom) := by
  intro h
  cases h
example : Sat alternating 1 (.next atom) := rfl

-- An until witness at the current position needs no left-operand proof.
theorem until_now : WordSat never (.until .falsehood (.neg atom)) := by
  refine ⟨0, Nat.le_refl 0, ?_, ?_⟩
  · intro h
    cases h
  · intro k _ hk
    exact (Nat.not_lt_zero k hk).elim

theorem eventually_now : WordSat alternating (Formula.eventually atom) := by
  refine ⟨0, Nat.le_refl 0, rfl, ?_⟩
  intro k _ hk
  exact (Nat.not_lt_zero k hk).elim

-- At position one, the witness is position two, rather than position zero.
theorem eventually_later : Sat alternating 1 (Formula.eventually atom) := by
  refine ⟨2, by decide, rfl, ?_⟩
  intro _ _ _ h
  exact h

-- Strong until cannot be satisfied by postponing the right operand forever.
theorem until_requires_right : ¬ WordSat always (.until atom .falsehood) := by
  intro ⟨_, _, h, _⟩
  exact h

theorem eventually_requires_witness : ¬ WordSat never (Formula.eventually atom) := by
  intro ⟨_, _, h, _⟩
  cases h

example : WordSat always (Formula.conj atom atom) := by
  intro h
  cases h with
  | inl h => exact h rfl
  | inr h => exact h rfl

example : WordSat never (Formula.imp atom atom) := Or.inl (by intro h; cases h)

theorem globally_constant : WordSat always (Formula.globally atom) := by
  intro ⟨_, _, h, _⟩
  exact h rfl

-- Release permits its left operand to remain false when the right holds forever.
theorem release_constant : WordSat always (Formula.release .falsehood atom) := by
  intro ⟨_, _, h, _⟩
  exact h rfl

-- This word has request at zero and grant from position one onward.
def requestThenGrant : Word Bool := ⟨fun i isGrant =>
  if isGrant then decide (1 ≤ i) else decide (i = 0)⟩

theorem until_later : WordSat requestThenGrant (.until (.atom false) (.atom true)) := by
  refine ⟨1, by decide, rfl, ?_⟩
  intro k _ hk
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  subst k
  rfl

-- A witness at one cannot skip a false left operand at position zero.
theorem until_checks_prefix :
    ¬ WordSat requestThenGrant (.until .falsehood (.atom true)) := by
  intro ⟨j, _, hj, hprefix⟩
  cases j with
  | zero => cases hj
  | succ n => exact hprefix 0 (Nat.le_refl 0) (Nat.zero_lt_succ n)

end Examples.Words
