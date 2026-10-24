import KILT
import Examples.Buchi
import Examples.TrafficLight

/-!
# Formula-input checker: proofs and execution tests

The small verdict theorems compute in the kernel. Larger cases below execute
compiled code and fail elaboration on unexpected results; those executions do
not create proofs. General correctness and monitor equivalence remain theorems.
-/
namespace Examples.Checker
open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL

def p : Formula Nat := .atom 0
def q : Formula Nat := .atom 1

/-- One serial state, with only atom zero true. -/
def singleton : FiniteKripke Unit Nat where
  initials := {()}
  initials_nonempty := by simp
  successors _ := {()}
  label _ a := a == 0

theorem singleton_serial : singleton.toKripke.Serial :=
  singleton.isSerial_eq_true_iff.mp (by decide)

theorem truth_verdict : singleton.check Formula.truth singleton_serial = true := by decide
theorem falsehood_verdict : singleton.check .falsehood singleton_serial = false := by decide
theorem atom_verdict : singleton.check p singleton_serial = true := by decide

/-- A kernel-computed verdict entails universal satisfaction via the main theorem. -/
theorem singleton_satisfies_atom : singleton.toKripke.Satisfies p :=
  (singleton.check_correct p singleton_serial).mp atom_verdict

theorem falsehood_counterexample :
    ∃ path : singleton.toKripke.Path, path.IsInitial ∧ ¬ WordSat path.word .falsehood :=
  (singleton.check_eq_false_iff .falsehood singleton_serial).mp falsehood_verdict

/-- True observes p, then moves to false observing q forever. Optionally start
in both states, to distinguish universal checking from existence of a good path. -/
def twoState (multiple : Bool := false) : FiniteKripke Bool Nat where
  initials := if multiple then {true, false} else {true}
  initials_nonempty := by cases multiple <;> simp
  successors _ := {false}
  label state a := if a = 0 then state else if a = 1 then !state else false

theorem twoState_serial (multiple : Bool) : (twoState multiple).toKripke.Serial := by
  intro state
  exact ⟨false, by simp [FiniteKripke.toKripke, twoState]⟩

theorem initial_atom_verdict : (twoState false).check p (twoState_serial false) = true := by
  decide
theorem multiple_initials_verdict : (twoState true).check p (twoState_serial true) = false := by
  decide

def deadlock : FiniteKripke Unit Nat where
  initials := {()}
  initials_nonempty := by simp
  successors _ := ∅
  label _ _ := false

theorem deadlock_not_serial : ¬ deadlock.toKripke.Serial := by
  intro h
  obtain ⟨s, hs⟩ := h ()
  exact (Finset.notMem_empty s) hs

/-- The lower-level graph search inserts no loop into an accepting deadlock. -/
theorem deadlock_no_accepted_path :
    deadlock.hasAcceptedPath (Formula.falsehood : Formula Nat).violationAutomaton = false := by
  decide

/-- This verdict is transported from a proved handwritten-monitor verdict;
it is not a second independent kernel computation of the compiled automaton. -/
theorem waiting_response_verdict :
    Examples.Buchi.waitingSystem.check Examples.RequestGrant.response
      Examples.Buchi.waitingSerial = false := by
  rw [Examples.Buchi.waitingSystem.check_eq_checkAgainst Examples.RequestGrant.response
    Examples.Buchi.waitingSerial
    (Monitors.notResponse Examples.Buchi.requestAtom Examples.Buchi.grantAtom)
    (Monitors.notResponse_accepts _ _)]
  exact Examples.Buchi.waiting_response_check

theorem waiting_response_counterexample :
    ∃ path : Examples.Buchi.waitingSystem.toKripke.Path,
      path.IsInitial ∧ ¬ WordSat path.word Examples.RequestGrant.response :=
  (Examples.Buchi.waitingSystem.check_eq_false_iff _ Examples.Buchi.waitingSerial).mp
    waiting_response_verdict

/-- Keep the timed compiled call behind an IO boundary. It returns no proof. -/
@[noinline] def executeCheck {S : Type} {AP : Type} [Fintype S] [DecidableEq S]
    [DecidableEq AP] (M : FiniteKripke S AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) : IO Bool := do
  return M.check φ hserial

/-- Unexpected results raise an IO error, which makes the #eval build fail. -/
def expectCheck {S : Type} {AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (expected : Bool) : IO Bool := do
  let started ← IO.monoMsNow
  let actual ← executeCheck M φ hserial
  let finished ← IO.monoMsNow
  let closure := (Formula.neg φ).normalize.subformulas.card
  let automaton := Fintype.card (Formula.AutomatonState (.neg φ))
  let product := Fintype.card S * automaton
  IO.println s!"check {name}: {actual}; closure={closure}, automaton={automaton}, product={product}, elapsed={finished - started}ms"
  if actual != expected then
    throw (IO.userError s!"Checker regression {name}: expected {expected}, got {actual}")
  return actual

def expectAgreement (name : String) (compiled monitor : Bool) : IO Unit := do
  if compiled != monitor then
    throw (IO.userError s!"Checker/monitor disagreement {name}: {compiled} versus {monitor}")
  IO.println s!"monitor {name}: matched"

def expectEventually {S : Type} {AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (atom : AP)
    (hserial : M.toKripke.Serial) (expected : Bool) : IO Unit := do
  let actual ← expectCheck name M (◇ (.atom atom)) hserial expected
  expectAgreement name actual (M.checkAgainst (Monitors.notEventually atom) hserial)

def expectResponse {S : Type} {AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (request grant : AP)
    (hserial : M.toKripke.Serial) (expected : Bool) : IO Unit := do
  let actual ← expectCheck name M (□ ((.atom request) ⟹ ◇ (.atom grant))) hserial expected
  expectAgreement name actual (M.checkAgainst (Monitors.notResponse request grant) hserial)

def runRegressionChecks : IO Unit := do
  expectEventually "request/grant cycle eventual grant" Examples.Buchi.cycleSystem
    Examples.Buchi.grantAtom Examples.Buchi.cycleSerial true
  expectEventually "request/grant waiting eventual grant" Examples.Buchi.waitingSystem
    Examples.Buchi.grantAtom Examples.Buchi.waitingSerial false
  expectResponse "request/grant cycle response" Examples.Buchi.cycleSystem
    Examples.Buchi.requestAtom Examples.Buchi.grantAtom Examples.Buchi.cycleSerial true
  expectResponse "request/grant waiting response" Examples.Buchi.waitingSystem
    Examples.Buchi.requestAtom Examples.Buchi.grantAtom Examples.Buchi.waitingSerial false
  expectEventually "traffic cycle eventual green" Examples.TrafficLight.controller
    Examples.TrafficLight.Colour.green Examples.TrafficLight.controller_serial true
  expectEventually "traffic stuck eventual green" Examples.TrafficLight.stuckController
    Examples.TrafficLight.Colour.green Examples.TrafficLight.stuckController_serial false
  expectResponse "traffic cycle red response" Examples.TrafficLight.controller
    Examples.TrafficLight.Colour.red Examples.TrafficLight.Colour.green
    Examples.TrafficLight.controller_serial true
  expectResponse "traffic stuck red response" Examples.TrafficLight.stuckController
    Examples.TrafficLight.Colour.red Examples.TrafficLight.Colour.green
    Examples.TrafficLight.stuckController_serial false
  let trafficSafety := □ (¬ₗ (Examples.TrafficLight.red ∧ₗ Examples.TrafficLight.green))
  discard <| expectCheck "traffic cycle safety" Examples.TrafficLight.controller trafficSafety
    Examples.TrafficLight.controller_serial true
  discard <| expectCheck "traffic stuck safety" Examples.TrafficLight.stuckController trafficSafety
    Examples.TrafficLight.stuckController_serial true
  let M := twoState false
  let serial := twoState_serial false
  discard <| expectCheck "initial-only p eventually" M (◇ p) serial true
  discard <| expectCheck "next sees q" M (𝒩 q) serial true
  discard <| expectCheck "next does not see initial p" M (𝒩 p) serial false
  discard <| expectCheck "until fulfilled at successor" M (p 𝒰 q) serial true
  discard <| expectCheck "until fulfilled immediately" M (.falsehood 𝒰 p) serial true
  discard <| expectCheck "release includes successor endpoint" M (Formula.release q p) serial false
  discard <| expectCheck "release ends immediately with right true" M (Formula.release p p) serial true
  discard <| expectCheck "multiple starts: p is not universal" (twoState true) p
    (twoState_serial true) false

#eval runRegressionChecks

end Examples.Checker
