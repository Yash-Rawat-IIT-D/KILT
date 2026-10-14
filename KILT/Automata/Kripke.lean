import KILT.Kripke.Semantics
import Cslib.Computability.Automata.NA.Basic

/-!
# Kripke structures as automata

This module will encode labelled Kripke transitions with CSLib automata types
and prove that initial paths correspond to runs over their observation words.
It is kept separate from the semantic definitions so the encoding cannot alter
their meaning.
-/

namespace KILT.Kripke

universe u v

variable {State : Type u} {AP : Type v}

/-- View a Kripke structure as a CSLib nondeterministic automaton. A transition
is labelled by the valuation of its source state. -/
def toNA (M : KILT.Kripke State AP) :
    Cslib.Automata.NA State (LTL.Valuation AP) where
  Tr s valuation t := M.step s t ∧ valuation = M.label s
  start := M.initial

/-- Runs of the encoding are exactly initial valid state sequences carrying
the model's source-state label word. -/
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

/-- A path's own observation word is a run precisely when the path starts in
an initial state. -/
theorem path_run_iff (M : KILT.Kripke State AP) (p : M.Path) :
    M.toNA.Run p.word p.states ↔ p.IsInitial := by
  constructor
  · intro run
    exact ((toNA_run_iff M p.word p.states).mp run).1
  · intro hinitial
    apply (toNA_run_iff M p.word p.states).mpr
    exact ⟨hinitial, p.valid, rfl⟩

/-- Kripke satisfaction agrees with satisfaction of every word carried by a
run of the CSLib encoding. No seriality assumption is needed. -/
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
