import KILT.Kripke.Basic
import KILT.LTL.Basic
import Cslib.Foundations.Data.OmegaSequence.Init

/-!
# Infinite Kripke paths

This module represents individual infinite executions of a Kripke structure,
their observation words, and their finite-prefix suffixes. Dropping a prefix
preserves transition validity but does not generally preserve initiality.
-/

namespace KILT.Kripke

universe u v

variable {State : Type u} {AP : Type v} {M : KILT.Kripke State AP}

/--
A single infinite execution of `M`. The states form a CSLib omega sequence,
and `valid` certifies that every consecutive pair follows `M.step`. Initiality
is deliberately separate because an execution or its suffix may begin at a
non-initial state.
-/
structure Path (M : KILT.Kripke State AP) where
  states : Cslib.ωSequence State
  valid : ∀ i, M.step (states i) (states (i + 1))

namespace Path

/-- An execution is initial when its first state is an initial state of `M`. -/
def IsInitial (p : Path M) : Prop := M.initial (p.states 0)

/--
The remaining execution after discarding its first `n` states. Transition
validity is reconstructed by shifting the original path's `valid` proof.
-/
def drop (p : Path M) (n : Nat) : Path M where
  states := p.states.drop n
  valid := by
    intro i
    change M.step (p.states (i + n)) (p.states ((i + 1) + n))
    simpa only [show (i + 1) + n = (i + n) + 1 by omega] using
      p.valid (i + n)

/--
The infinite valuation word observed along an execution, obtained by mapping
`M.label` over its state sequence. Position zero labels the first path state.
-/
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

/--
Internal choice function that turns relational seriality into a stream
generator by selecting one successor of each state. The selection is arbitrary
and noncomputable: it supplies a semantic witness, not an execution policy or
graph-search algorithm.
-/
private noncomputable def successor (h : M.Serial) (s : State) : State :=
  Classical.choose (h s)

/--
The state selected by `successor` is connected by `M.step`. This is the proof
used to fill `Path.valid` when the choice function is iterated.
-/
private theorem step_successor (h : M.Serial) (s : State) :
    M.step s (successor h s) := Classical.choose_spec (h s)

/--
Concretize seriality into one infinite execution beginning at `s` by repeatedly
applying the internally chosen successor. This witnesses that a serial
relational model can continue forever; it is a classical semantic construction,
not an executable search through all possible executions.
-/
noncomputable def fromState (h : M.Serial) (s : State) : Path M where
  states := Cslib.ωSequence.iterate (successor h) s
  valid := by
    intro i
    rw [show i + 1 = Nat.succ i by omega,
      Cslib.ωSequence.get_succ_iterate']
    exact step_successor h _

/-- The constructed execution begins at the state supplied to `fromState`. -/
@[simp] theorem fromState_zero (h : M.Serial) (s : State) :
    (fromState h s).states 0 = s := rfl

/--
Combine `initial_nonempty` with `fromState` to obtain one initial infinite
execution. Thus seriality makes the path quantification in Kripke satisfaction
nonempty rather than merely ruling out individual deadlocks.
-/
theorem exists_initial (h : M.Serial) : ∃ p : Path M, p.IsInitial := by
  rcases M.initial_nonempty with ⟨s, hs⟩
  exact ⟨fromState h s, hs⟩

end Path

end KILT.Kripke
