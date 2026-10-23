import Examples.Buchi
import Examples.TrafficLight
import Lean.Util.CollectAxioms

/-!
# Build-failing trust audit

Inspect transitive axiom dependencies, rather than just scanning source text.
This module is part of the default Examples target, including CI builds.
Existing native_decide examples are retained elsewhere; new principal backend
proofs and kernel-computed verdicts must use only standard Lean axioms.
-/
namespace Examples.BuchiTrust

/-- Reject unfinished proofs and any additional axiom in the named results. -/
def auditStandardAxioms (declarations : Array Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for declaration in declarations do
    unless (← Lean.getEnv).contains declaration do
      throwError "Axiom audit failed: declaration {declaration} is missing"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Axiom audit failed: {declaration} depends on {axiomName}"
    Lean.logInfo m!"Axiom audit passed: {declaration}: {axioms.toList}"

run_cmd auditStandardAxioms #[
  ``KILT.Graph.hasAcceptingCycle_eq_true_iff,
  ``KILT.Graph.hasAcceptingCycle_iff_hasAcceptingRun,
  ``KILT.Graph.hasAcceptingCycle_eq_true_iff_run,
  ``KILT.Automata.FiniteBuchi.toBuchi_start,
  ``KILT.Automata.FiniteBuchi.toBuchi_transition,
  ``KILT.Automata.FiniteBuchi.toBuchi_accept,
  ``KILT.FiniteKripke.product_run_iff,
  ``KILT.FiniteKripke.hasAcceptedPath_eq_true_iff,
  ``KILT.FiniteKripke.checkAgainst_correct,
  ``KILT.Automata.Monitors.guessAndStay_accepts,
  ``KILT.Automata.Monitors.eventually_accepts,
  ``KILT.Automata.Monitors.notEventually_accepts,
  ``KILT.Automata.Monitors.notResponse_accepts,
  ``Examples.Buchi.cycle_eventually_check,
  ``Examples.Buchi.waiting_eventually_check,
  ``Examples.Buchi.cycle_response_check,
  ``Examples.Buchi.waiting_response_check,
  ``Examples.Buchi.cycle_eventually_from_checker,
  ``Examples.Buchi.waiting_eventually_from_checker,
  ``Examples.Buchi.cycle_response_from_checker,
  ``Examples.Buchi.waiting_response_from_checker,
  ``KILT.LTL.sat_drop,
  ``KILT.Graph.mem_reachableSet_iff,
  ``KILT.Graph.route?_sound,
  ``KILT.Kripke.satisfies_iff_all_runs,
  ``Examples.TrafficLight.red_until_green,
  ``Examples.TrafficLight.not_green_release_red,
  ``Examples.TrafficLight.controller_safe,
  ``Examples.TrafficLight.stuckController_safe,
  ``Examples.TrafficLight.controller_ordered,
  ``Examples.TrafficLight.controller_eventually_check,
  ``Examples.TrafficLight.stuck_eventually_check,
  ``Examples.TrafficLight.controller_response_check,
  ``Examples.TrafficLight.stuck_response_check,
  ``Examples.TrafficLight.controller_eventually_green,
  ``Examples.TrafficLight.controller_red_responds,
  ``Examples.TrafficLight.stuck_not_eventually_green,
  ``Examples.TrafficLight.stuck_not_red_responds]

end Examples.BuchiTrust
