import Examples.Buchi
import Examples.TrafficLight
import Examples.Normalization
import Examples.GeneralizedBuchi
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
  ``Examples.TrafficLight.stuck_not_red_responds,
  ``KILT.LTL.NNF.negate_negate,
  ``KILT.LTL.NNF.sat_negate,
  ``KILT.LTL.Formula.sat_normalize,
  ``KILT.LTL.Formula.sat_normalize_neg,
  ``KILT.LTL.Formula.wordSat_normalize,
  ``KILT.LTL.NNF.mem_subformulas_iff,
  ``KILT.LTL.NNF.mem_subformulas_self,
  ``KILT.LTL.NNF.child_subformulas_subset,
  ``KILT.LTL.NNF.subformulas_subset_of_mem,
  ``KILT.LTL.NNF.child_size_lt,
  ``KILT.LTL.NNF.size_le_of_mem,
  ``KILT.LTL.NNF.card_subformulas_le_size,
  ``Examples.Normalization.model_normalization,
  ``Examples.Normalization.traffic_safety,
  ``Examples.Normalization.traffic_ordering,
  ``Examples.Normalization.traffic_stuck_response,
  ``Examples.Normalization.until_now,
  ``Examples.Normalization.no_postponed_until,
  ``Examples.Normalization.release_forever,
  ``Examples.Normalization.release_endpoint,
  ``KILT.Automata.RoundRobin.complete,
  ``KILT.Automata.RoundRobin.sound,
  ``KILT.Automata.FiniteGeneralizedBuchi.toNA_start,
  ``KILT.Automata.FiniteGeneralizedBuchi.toNA_transition,
  ``KILT.Automata.FiniteGeneralizedBuchi.accepts_family_ext,
  ``KILT.Automata.FiniteGeneralizedBuchi.converted_start,
  ``KILT.Automata.FiniteGeneralizedBuchi.converted_transition,
  ``KILT.Automata.FiniteGeneralizedBuchi.converted_accept,
  ``KILT.Automata.FiniteGeneralizedBuchi.lift_run,
  ``KILT.Automata.FiniteGeneralizedBuchi.project_run,
  ``KILT.Automata.FiniteGeneralizedBuchi.run_eq_lift,
  ``KILT.Automata.FiniteGeneralizedBuchi.accepts_singleton,
  ``KILT.Automata.FiniteGeneralizedBuchi.counter_acceptance,
  ``KILT.Automata.FiniteGeneralizedBuchi.lift_acceptingRun,
  ``KILT.Automata.FiniteGeneralizedBuchi.toFiniteBuchi_accepts,
  ``KILT.FiniteKripke.hasAcceptedPath_generalized_iff,
  ``Examples.GeneralizedBuchi.verdict_correct,
  ``Examples.GeneralizedBuchi.reordered,
  ``Examples.GeneralizedBuchi.controller_recurs,
  ``Examples.GeneralizedBuchi.redOnly_does_not_recur,
  ``Examples.GeneralizedBuchi.controller_has_recurring_path]

end Examples.BuchiTrust
