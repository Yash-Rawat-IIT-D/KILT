import KILT.Kripke.Semantics
import Cslib.Computability.Automata.NA.Basic

/-!
# Kripke structures as automata

This module encodes labelled Kripke transitions with CSLib automata types. The
encoding preserves the behavior of the model: an initial Kripke path paired
with its observation word is exactly a run of the automaton. Consequently,
universal satisfaction over initial paths can equivalently be stated as
satisfaction of every word carried by an automaton run.
-/

namespace KILT.Kripke

universe u v

variable {State : Type u} {AP : Type v}

/-- Model a Kripke structure as a CSLib nondeterministic automaton. Automaton
states and initial states are those of the Kripke structure, while each
transition must follow `M.step` and consume the source state's label. Thus an
automaton run represents a model execution together with its observed label
sequence. -/
def toNA (M : KILT.Kripke State AP) :
    Cslib.Automata.NA State (LTL.Valuation AP) where
  Tr s valuation t := M.step s t ∧ valuation = M.label s
  start := M.initial

/-- A state sequence is a run of the encoding exactly when it starts in an
initial Kripke state, follows valid model steps, and reads the infinite word of
source-state labels observed along that execution. -/
theorem toNA_run_iff (M : KILT.Kripke State AP) (word : LTL.Word AP)
    (states : Cslib.ωSequence State) :
    M.toNA.Run word states ↔
      M.initial (states 0) ∧
      (∀ i, M.step (states i) (states (i + 1))) ∧
      word = states.map M.label := by
  constructor
  · intro run
    refine ⟨run.start, fun i => (run.trans i).1, ?_⟩
    apply Cslib.ωSequence.ext
    intro i
    exact (run.trans i).2
  · rintro ⟨hstart, hstep, rfl⟩
    exact { start := hstart, trans := fun i => ⟨hstep i, rfl⟩ }

/-- A `Path` already supplies the valid Kripke steps required by a run, and
`p.word` already supplies their source-state labels. The remaining requirement
is exactly that the path starts in an initial state. -/
theorem path_run_iff (M : KILT.Kripke State AP) (p : M.Path) :
    M.toNA.Run p.word p.states ↔ p.IsInitial := by
  constructor
  · intro run
    exact ((toNA_run_iff M p.word p.states).mp run).1
  · intro hinitial
    apply (toNA_run_iff M p.word p.states).mpr
    exact ⟨hinitial, p.valid, rfl⟩

/-- Through the path--run correspondence, requiring every initial model path
to satisfy a formula is equivalent to requiring every word and state sequence
forming an automaton run to satisfy it. -/
theorem satisfies_iff_all_runs (M : KILT.Kripke State AP)
    (formula : LTL.Formula AP) :
    M.Satisfies formula ↔
      ∀ word states, M.toNA.Run word states → LTL.WordSat word formula := by
  constructor
  · intro hsatisfies word states run
    have hchar := (toNA_run_iff M word states).mp run
    let p : M.Path := ⟨states, hchar.2.1⟩
    have hp := hsatisfies p hchar.1
    rw [hchar.2.2]
    exact hp
  · intro hruns p hp
    exact hruns p.word p.states ((path_run_iff M p).mpr hp)

end KILT.Kripke
