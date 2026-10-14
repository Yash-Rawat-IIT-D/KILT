import KILT.Kripke.Basic
import KILT.LTL.Basic
import Cslib.Foundations.Data.OmegaSequence.Init

/-!
# Infinite Kripke paths

This module will define valid infinite paths, initial paths, path suffixes, and
their observation words.  Dropping a path prefix preserves transition validity
but does not in general preserve its initial-state proof.
-/

namespace KILT.Kripke

universe u v

variable {State : Type u} {AP : Type v} {M : KILT.Kripke State AP}

/-- An infinite state sequence whose adjacent states follow the transition
relation. Initiality is deliberately kept separate. -/
structure Path (M : KILT.Kripke State AP) where
  states : Cslib.ωSequence State
  valid : ∀ i, M.step (states i) (states (i + 1))

namespace Path

/-- The first state of the path is an initial state of the model. -/
def IsInitial (p : Path M) : Prop := M.initial (p.states 0)

/-- Drop a finite prefix of a valid path. -/
def drop (p : Path M) (n : Nat) : Path M where
  states := p.states.drop n
  valid := by
    intro i
    change M.step (p.states (i + n)) (p.states ((i + 1) + n))
    simpa only [show (i + 1) + n = (i + n) + 1 by omega] using
      p.valid (i + n)

/-- The valuation word observed along a path. Position zero observes the
path's first state. -/
def word (p : Path M) : LTL.Word AP := p.states.map M.label

@[simp] theorem word_apply (p : Path M) (i : Nat) :
    p.word i = M.label (p.states i) := rfl

@[simp] theorem drop_states_apply (p : Path M) (n i : Nat) :
    (p.drop n).states i = p.states (n + i) := by
  change p.states (i + n) = p.states (n + i)
  rw [Nat.add_comm]

/-- Observing a path suffix is the suffix of the original observation word. -/
theorem word_drop (p : Path M) (n : Nat) :
    (p.drop n).word = p.word.drop n := by
  apply Cslib.ωSequence.ext
  intro i
  rfl

/-- A suffix starts initially exactly when the state at the cut is initial. -/
@[simp] theorem drop_isInitial (p : Path M) (n : Nat) :
    (p.drop n).IsInitial ↔ M.initial (p.states n) := by
  simp only [IsInitial, drop_states_apply, Nat.add_zero]

/-- LTL at the start of a path suffix is LTL at the corresponding position of
the original path word. -/
theorem wordSat_drop (p : Path M) (n : Nat) (formula : LTL.Formula AP) :
    LTL.WordSat (p.drop n).word formula ↔ LTL.Sat p.word n formula := by
  rw [word_drop, LTL.wordSat_drop]

private noncomputable def successor (h : M.Serial) (s : State) : State :=
  Classical.choose (h s)

private theorem step_successor (h : M.Serial) (s : State) :
    M.step s (successor h s) := Classical.choose_spec (h s)

/-- Seriality supplies an infinite path beginning at any chosen state. This is
a classical semantic construction, not an executable search procedure. -/
noncomputable def fromState (h : M.Serial) (s : State) : Path M where
  states := Cslib.ωSequence.iterate (successor h) s
  valid := by
    intro i
    rw [show i + 1 = Nat.succ i by omega,
      Cslib.ωSequence.get_succ_iterate']
    exact step_successor h _

@[simp] theorem fromState_zero (h : M.Serial) (s : State) :
    (fromState h s).states 0 = s := rfl

/-- A serial model has an initial infinite path because its initial set is
nonempty. -/
theorem exists_initial (h : M.Serial) : ∃ p : Path M, p.IsInitial := by
  rcases M.initial_nonempty with ⟨s, hs⟩
  exact ⟨fromState h s, hs⟩

end Path

end KILT.Kripke
