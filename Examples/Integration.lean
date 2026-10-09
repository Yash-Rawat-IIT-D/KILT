import Cslib.Foundations.Data.OmegaSequence.Defs
import Cslib.Computability.Automata.NA.Basic
import Cslib.Computability.Automata.NA.Prod

/-!
# CSLib integration checks

Keep the audited sequence, nondeterministic-automaton, and product APIs in
the default build. These are compatibility checks, not KILT's Kripke encoding.
-/

namespace Examples.Integration

open Cslib Cslib.Automata

/-- One state, initially present, with a transition for every Boolean symbol. -/
def loop : NA Unit Bool where
  Tr _ _ _ := True
  start _ := True

example : loop.Run (ωSequence.const true) (ωSequence.const ()) :=
  ⟨True.intro, fun _ => True.intro⟩

-- Exercise the actual product API and its correspondence theorem.
example : (NA.iProd (fun _ : Bool => loop)).Run
    (ωSequence.const true) (ωSequence.const (fun _ : Bool => ())) := by
  apply NA.iProd_run_iff.mpr
  intro _
  exact ⟨True.intro, fun _ => True.intro⟩

end Examples.Integration
