import Examples.Counterexample

/-!
# Compile once, prepare once, query twice

General correctness is proved in the library. Small propositions below use
kernel-checked refinement/equality proofs; build-failing displays exercise the
compiled methods. No timings, persistent cache or native proof oracle.
-/
namespace Examples.PreparedChecking
open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL
set_option synthInstance.maxSize 1024
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def unitOrder := Examples.Counterexample.unitOrder
def boolOrder := Examples.Counterexample.boolOrder

def loopSearch := Graph.prepareSearch unitOrder {()} (fun _ => {()}) {()}
def emptySeeds := Graph.prepareSearch unitOrder ∅ (fun _ => {()}) {()}
def emptyAcceptance := Graph.prepareSearch unitOrder {()} (fun _ => {()}) ∅
def deadlockSearch := Graph.prepareSearch unitOrder {()} (fun _ => ∅) {()}

theorem loop_verdict : loopSearch.hasAcceptingCycle = true := by
  rw [Graph.PreparedSearch.hasAcceptingCycle_eq, Graph.hasAcceptingCycle_eq_spec]
  decide

theorem loop_shape : Examples.LassoGraph.shape loopSearch.acceptingLasso? = some ([], [()]) := by
  rw [Graph.PreparedSearch.acceptingLasso?_eq, Graph.acceptingLasso?_eq_spec]
  decide

theorem empty_seeds_skip :
    (match emptySeeds with | .empty _ => true | .ready _ => false) = true := by decide

theorem empty_acceptance_skip :
    (match emptyAcceptance with | .empty _ => true | .ready _ => false) = true := by decide

theorem accepting_deadlock : deadlockSearch.acceptingLasso? = none := by
  rw [Graph.PreparedSearch.acceptingLasso?_eq, Graph.acceptingLasso?_eq_spec]
  decide

/-- The order and seriality proof are supplied once for all this model's jobs. -/
def execution := Checker.singleton.checker Checker.singleton_serial unitOrder
def good := execution.prepare Checker.p
def bad := execution.prepare (Formula.falsehood : Formula Nat)

theorem good_verdict : good.check = true := by
  rw [FiniteKripke.PreparedCheck.check_eq_check]
  exact Checker.atom_verdict

theorem bad_verdict : bad.check = false := by
  rw [FiniteKripke.PreparedCheck.check_eq_check]
  exact Checker.falsehood_verdict

theorem good_no_witness : good.counterexample? = none :=
  good.counterexample?_eq_none_iff.mpr (good.check_correct.mp good_verdict)

theorem bad_has_witness : bad.counterexample?.isSome = true :=
  bad.counterexample?_isSome_iff.mpr bad_verdict

/-- The new interface preserves the exact legacy product-state witness. -/
theorem exact_legacy_witness : bad.counterexample? =
    Checker.singleton.counterexample? .falsehood Checker.singleton_serial unitOrder := rfl

/-- Soundness is about this witness's own sequence, not a separate existence path. -/
theorem actual_violating_trace : ∃ l, ∃ h : bad.counterexample? = some l,
    (bad.counterexamplePath l h).IsInitial ∧
      ¬ WordSat (bad.counterexamplePath l h).word .falsehood := by
  obtain ⟨l, h⟩ := Option.isSome_iff_exists.mp bad_has_witness
  exact ⟨l, h, bad.counterexample?_sound h⟩

def compiledViolation := (Formula.neg Checker.p).compile
def reusedSingleton := execution.prepareCompiled compiledViolation
def reusedMultiple := ((Checker.twoState true).checker
  (Checker.twoState_serial true) boolOrder).prepareCompiled compiledViolation

theorem compiled_language (word : Word Nat) :
    Cslib.Automata.ωAcceptor.Accepts compiledViolation.automaton.toCSLib word ↔
      ¬ WordSat word Checker.p := compiledViolation.accepts_iff word

theorem reused_singleton : reusedSingleton.check = true := by
  rw [FiniteKripke.PreparedCheck.check_eq_check]
  exact Checker.atom_verdict

theorem reused_multiple : reusedMultiple.check = false := by
  rw [FiniteKripke.PreparedCheck.check_eq_check]
  exact Checker.multiple_initials_verdict

def reverseBool : Graph.Enumeration Bool := Graph.Enumeration.ofList [true, false] (by decide)
theorem order_independent :
    (((Checker.twoState true).checker (Checker.twoState_serial true) boolOrder).prepare Checker.p).check =
    (((Checker.twoState true).checker (Checker.twoState_serial true) reverseBool).prepare Checker.p).check :=
  FiniteKripke.PreparedCheck.check_eq _ _

/-- The monitor layer still permits partial models and empty automata. -/
def emptyMonitor : FiniteBuchi (Fin 0) (Valuation Nat) where
  initials := ∅
  successors q := nomatch q
  accepting := ∅

theorem partial_empty_product :
    (Checker.deadlock.prepareProduct emptyMonitor unitOrder (Graph.Enumeration.fin 0)).acceptingLasso? = none :=
  by decide

section DerivedFintype
inductive Switch where | off | on deriving DecidableEq

def switchOrder : Graph.Enumeration Switch :=
  Graph.Enumeration.ofList [.off, .on] (by intro s; cases s <;> simp)

local instance : Fintype Switch := switchOrder.fintype

def switches : FiniteKripke Switch Nat where
  initials := {.off}
  initials_nonempty := by simp
  successors s := {s}
  label _ a := a == 0

theorem switches_serial : switches.toKripke.Serial := by
  intro s
  exact ⟨s, by simp [FiniteKripke.toKripke, switches]⟩

def switchesProblem := (switches.checker switches_serial switchOrder).prepare Checker.p
theorem derived_finiteness : Fintype.card Switch = 2 := by decide
end DerivedFintype

def expect (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"prepared checking: {name}")

def verify {S AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    {M : FiniteKripke S AP} {φ : Formula AP}
    (name : String) (problem : FiniteKripke.PreparedCheck M φ) (expected : Bool) : IO Unit := do
  -- Both operations consume this one prepared product; neither prepares it again.
  let verdict := problem.check
  let witness := problem.counterexample?
  expect (name ++ " verdict") (verdict == expected)
  expect (name ++ " witness presence") (witness.isSome == !expected)
  if let some l := witness then
    expect (name ++ " finite certificate")
      (Counterexample.certificateValid (M.productInitials problem.compiled.automaton)
        (M.productSuccessors problem.compiled.automaton)
        (FiniteKripke.productAccepting problem.compiled.automaton) l)
    let projected := l.map Prod.fst
    expect (name ++ " projection timing") (projected.replay 8 == (l.replay 8).map Prod.fst)
    IO.println s!"prepared {name}: {verdict}; prefix={l.prefix.length}, loop={l.loop.length}"
  else IO.println s!"prepared {name}: {verdict}; no counterexample"

def runReuse : IO Unit := do
  let query := Graph.prepareSearch unitOrder {()} (fun _ => {()}) {()}
  let answer := query.hasAcceptingCycle
  let witness := Graph.PreparedSearch.acceptingLasso? query
  expect "shared graph Boolean" answer
  expect "shared graph lasso" (Examples.LassoGraph.shape witness == some ([], [()]))
  let compiled := (Formula.neg Checker.p).compile
  verify "compiled reuse/singleton" (execution.prepareCompiled compiled) true
  verify "compiled reuse/multiple starts"
    (((Checker.twoState true).checker (Checker.twoState_serial true) boolOrder).prepareCompiled compiled) false
  verify "falsehood" (execution.prepare .falsehood) false
  verify "initial-position eventuality"
    (((Checker.twoState false).checker (Checker.twoState_serial false) boolOrder).prepare (◇ Checker.p)) true
  verify "next sees successor"
    (((Checker.twoState false).checker (Checker.twoState_serial false) boolOrder).prepare (𝒩 Checker.p)) false
  letI : Fintype Switch := switchOrder.fintype
  verify "finiteness from order" switchesProblem true

#eval runReuse

#eval do
  let order := Counterexample.requestOrder
  let cycle := Buchi.cycleSystem.checker Buchi.cycleSerial order
  let waiting := Buchi.waitingSystem.checker Buchi.waitingSerial order
  let compiled := (Formula.neg RequestGrant.response).compile
  verify "cycle response" (cycle.prepareCompiled compiled) true
  verify "waiting response" (waiting.prepareCompiled compiled) false
  let traffic := TrafficLight.controller.checker TrafficLight.controller_serial Counterexample.trafficOrder
  let stuck := TrafficLight.stuckController.checker TrafficLight.stuckController_serial Counterexample.trafficOrder
  let compiledTraffic := (Formula.neg TrafficLight.redResponds).compile
  verify "traffic response" (traffic.prepareCompiled compiledTraffic) true
  verify "stuck traffic response" (stuck.prepareCompiled compiledTraffic) false

end Examples.PreparedChecking
