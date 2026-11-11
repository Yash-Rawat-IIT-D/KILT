import KILT.LTL.Semantics

/-!
# Basic LTL semantic laws

This module derives reusable laws from KILT's indexed infinite-word semantics.
It proceeds from direct constructor and connective characterizations to
current-position consequences, one-step temporal unfoldings, and suffix laws.
No result here requires a finite atom type or decidable atom equality.

The proofs are independently written for KILT's indexed semantics. The design
reference remains LeanLTL's temporal definitions and laws:
https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean
-/

namespace KILT.LTL

universe u

variable {AP : Type u} {word : Word AP} {i : Nat}
variable {left right : Formula AP}

/-!
## Constructor semantics

These lemmas expose the defining clauses of `Sat` and its position-zero
specialization `WordSat`.
-/

@[simp] theorem sat_falsehood : Sat word i .falsehood ↔ False := Iff.rfl

@[simp] theorem sat_atom (a : AP) : Sat word i (.atom a) ↔ word i a = true := Iff.rfl

@[simp] theorem sat_neg : Sat word i (.neg left) ↔ ¬ Sat word i left := Iff.rfl

@[simp] theorem sat_disj :
    Sat word i (.disj left right) ↔ Sat word i left ∨ Sat word i right := Iff.rfl

@[simp] theorem sat_next : Sat word i (.next left) ↔ Sat word (i + 1) left := Iff.rfl

/-- The witness is at or after `i`; the left operand's interval excludes it. -/
theorem sat_until : Sat word i (.until left right) ↔
    ∃ j, i ≤ j ∧ Sat word j right ∧ ∀ k, i ≤ k → k < j → Sat word k left := Iff.rfl

@[simp] theorem wordSat_iff : WordSat word left ↔ Sat word 0 left := Iff.rfl

/-!
## Derived connectives

The following laws reduce KILT's derived Boolean and temporal connectives to
their direct semantic meanings.
-/

@[simp] theorem sat_truth : Sat word i Formula.truth ↔ True := by
  simp [Formula.truth]

@[simp] theorem sat_neg_neg : Sat word i (.neg (.neg left)) ↔ Sat word i left := by
  classical
  simp

@[simp] theorem sat_conj :
    Sat word i (Formula.conj left right) ↔ Sat word i left ∧ Sat word i right := by
  classical
  simp only [Formula.conj, sat_neg, sat_disj]
  tauto

@[simp] theorem sat_imp :
    Sat word i (Formula.imp left right) ↔ (Sat word i left → Sat word i right) := by
  classical
  simp only [Formula.imp, sat_disj, sat_neg]
  tauto

/-- Eventually permits a witness now, not just at a strictly later position. -/
@[simp] theorem sat_eventually : Sat word i (Formula.eventually left) ↔
    ∃ j, i ≤ j ∧ Sat word j left := by
  simp [Formula.eventually, sat_until]

/-- Globally includes the current position and every later one. -/
@[simp] theorem sat_globally : Sat word i (Formula.globally left) ↔
    ∀ j, i ≤ j → Sat word j left := by
  classical
  simp [Formula.globally]

/-- The right operand holds whenever the left has not held strictly earlier. -/
theorem sat_release : Sat word i (Formula.release left right) ↔
    ∀ j, i ≤ j → (∀ k, i ≤ k → k < j → ¬ Sat word k left) → Sat word j right := by
  classical
  simp only [Formula.release, sat_neg, sat_until]
  constructor
  · intro h j hij hprefix
    by_contra hright
    exact h ⟨j, hij, hright, hprefix⟩
  · intro h counterexample
    rcases counterexample with ⟨j, hij, hright, hprefix⟩
    exact hright (h j hij hprefix)

/-!
## Current-position consequences

These small lemmas record the immediate cases of the temporal operators:
strong until and eventually hold when their goal holds now, while global
satisfaction implies satisfaction now. Here `_now` is a local descriptive
suffix for position `i`, not a special Lean naming convention.
-/

/-- Until is already satisfied when its right operand holds now. -/
theorem sat_until_now (h : Sat word i right) : Sat word i (.until left right) := by
  refine ⟨i, Nat.le_refl i, h, ?_⟩
  intro k hlow hhigh
  omega

/-- Eventually follows immediately from satisfaction at the current position. -/
theorem sat_eventually_now (h : Sat word i left) :
    Sat word i (Formula.eventually left) :=
  sat_eventually.mpr ⟨i, Nat.le_refl i, h⟩

/-- A globally satisfied formula holds at the current position. -/
theorem sat_globally_now (h : Sat word i (Formula.globally left)) : Sat word i left :=
  sat_globally.mp h i (Nat.le_refl i)

/-!
## One-step temporal unfoldings

These equations restate the indexed denotational semantics as recursive
current/next-position characterizations. Until either reaches its right operand
now or preserves its left operand and continues. Release requires its right
operand now and is either released by its left operand or continues. Globally
requires its operand now and continues globally at the next position.

Note - These equivalent laws are deliberately not simp rules because each right-hand
side can retain the same temporal operator at the next position. For example,
unfolding `Sat word i (Formula.globally p)` once produces the current `p`
obligation and `Sat word (i + 1) (Formula.globally p)`. Automatically unfolding
the latter would produce obligations at `i + 1`, then `i + 2`, and so on.
Explicit rewriting keeps that expansion finite and under the proof author's
control.
-/

/-- One-step unfolding of strong until; an eventual witness is still required. -/
theorem sat_until_unfold : Sat word i (.until left right) ↔
    Sat word i right ∨ (Sat word i left ∧ Sat word (i + 1) (.until left right)) := by
  constructor
  · rintro ⟨j, hij, hright, hprefix⟩
    by_cases hji : j = i
    · left
      simpa only [hji] using hright
    · right
      refine ⟨hprefix i (Nat.le_refl i) (by omega), j, by omega, hright, ?_⟩
      intro k hlow hhigh
      exact hprefix k (by omega) hhigh
  · rintro (hright | ⟨hleft, hnext⟩)
    · exact sat_until_now hright
    · rcases hnext with ⟨j, hij, hright, hprefix⟩
      refine ⟨j, by omega, hright, ?_⟩
      intro k hlow hhigh
      by_cases hki : k = i
      · simpa only [hki] using hleft
      · exact hprefix k (by omega) hhigh

/-- One-step release unfolding, including its right operand at the endpoint. -/
theorem sat_release_unfold : Sat word i (Formula.release left right) ↔
    Sat word i right ∧ (Sat word i left ∨
      Sat word (i + 1) (Formula.release left right)) := by
  classical
  conv_lhs => rw [Formula.release, sat_neg, sat_until_unfold]
  simp only [Formula.release, sat_neg]
  tauto

/-- One-step global unfolding into the current obligation and its continuation. -/
theorem sat_globally_unfold : Sat word i (Formula.globally left) ↔
    Sat word i left ∧ Sat word (i + 1) (Formula.globally left) := by
  simp only [sat_globally]
  constructor
  · intro h
    exact ⟨h i (Nat.le_refl i), fun j hj => h j (by omega)⟩
  · rintro ⟨hnow, hnext⟩ j hj
    by_cases hji : j = i
    · simpa only [hji] using hnow
    · exact hnext j (by omega)

/-!
## Suffix manipulation

Dropping a finite prefix turns position `i` of the suffix into position `n + i`
of the original word. These lemmas let later proofs move temporal obligations
between a complete execution and the execution remaining after a finite prefix;
`wordSat_drop` is the common position-zero specialization.
-/

/-- Dropping a prefix shifts all satisfaction positions by the prefix length. -/
@[simp] theorem sat_drop (word : Word AP) (n i : Nat) (formula : Formula AP) :
    Sat (word.drop n) i formula ↔ Sat word (n + i) formula := by
  induction formula generalizing i with
  | falsehood => rfl
  | atom a =>
    change word (i + n) a = true ↔ word (n + i) a = true
    rw [Nat.add_comm i n]
  | neg operand ih => simp only [sat_neg, ih]
  | disj left right ihLeft ihRight => simp only [sat_disj, ihLeft, ihRight]
  | next operand ih => simp only [sat_next, ih, Nat.add_assoc]
  | «until» left right ihLeft ihRight =>
    simp only [sat_until, ihLeft, ihRight]
    constructor
    · rintro ⟨j, hij, hright, hprefix⟩
      refine ⟨n + j, by omega, hright, ?_⟩
      intro k hlow hhigh
      have hnk : n ≤ k := by omega
      have hshift : n + (k - n) = k := by omega
      have hleft := hprefix (k - n) (by omega) (by omega)
      simpa only [hshift] using hleft
    · rintro ⟨j, hij, hright, hprefix⟩
      have hnj : n ≤ j := by omega
      have hshift : n + (j - n) = j := by omega
      refine ⟨j - n, by omega, ?_, ?_⟩
      · simpa only [hshift] using hright
      · intro k hlow hhigh
        exact hprefix (n + k) (by omega) (by omega)

/-- Satisfaction at zero on a suffix is satisfaction at its starting position. -/
@[simp] theorem wordSat_drop (word : Word AP) (n : Nat) (formula : Formula AP) :
    WordSat (word.drop n) formula ↔ Sat word n formula := by
  simp [sat_drop word n 0 formula]

end KILT.LTL
