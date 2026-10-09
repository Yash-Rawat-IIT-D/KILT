import KILT.LTL.Semantics

/-!
# Basic LTL semantic laws

Semantic laws for the constructor basis, derived connectives, and word
suffixes. Until unfolding is deliberately not a simp rule: repeated unfolding
would keep introducing next-position obligations.

Until and eventually include the current position. Release requires its right
operand at every position before and including the first occurrence of its
left operand; if the left never occurs, the right must hold forever. These are
laws of infinite-word semantics, with no finiteness or atom-equality assumption.

The proofs are independently written for KILT's indexed semantics. The design
reference remains LeanLTL's temporal definitions and laws:
https://github.com/UCSCFormalMethods/LeanLTL/blob/d5473f06ab9d0ea652a51b2e78b11089731c4b6c/LeanLTL/TraceSet/Basic.lean
-/

namespace KILT.LTL

universe u

variable {AP : Type u} {word : Word AP} {i : Nat}
variable {left right : Formula AP}

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

/-- Until is already satisfied when its right operand holds now. -/
theorem sat_until_now (h : Sat word i right) : Sat word i (.until left right) := by
  refine ⟨i, Nat.le_refl i, h, ?_⟩
  intro k hlow hhigh
  omega

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

/-- Eventually follows immediately from satisfaction at the current position. -/
theorem sat_eventually_now (h : Sat word i left) :
    Sat word i (Formula.eventually left) :=
  sat_eventually.mpr ⟨i, Nat.le_refl i, h⟩

/-- A globally satisfied formula holds at the current position. -/
theorem sat_globally_now (h : Sat word i (Formula.globally left)) : Sat word i left :=
  sat_globally.mp h i (Nat.le_refl i)

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
