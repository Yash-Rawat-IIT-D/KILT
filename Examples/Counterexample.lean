import KILT.Kripke.Counterexample
import Examples.Checker
import Examples.TwoThreadLock
import Examples.LassoGraph

/-!
# Counterexamples: finite data, infinite violations

Small extraction assertions below are kernel computations. Larger demonstrations
execute and fail the build on unexpected presence or invalid finite certificates;
these executions create no proof. General soundness validates the actual returned
trace. Lock examples use small monitors whose violation languages are proved.
-/
namespace Examples.Counterexample
open KILT KILT.LTL KILT.Automata Cslib.Automata
open scoped KILT.LTL
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1024

def unitOrder : Graph.Enumeration Unit := Examples.LassoGraph.unitOrder
def boolOrder : Graph.Enumeration Bool := Graph.Enumeration.ofList [false, true] (by decide)
def requestOrder : Graph.Enumeration Examples.RequestGrant.State :=
  Graph.Enumeration.ofList [.waiting, .granting] (by intro s; cases s <;> simp)
def trafficOrder : Graph.Enumeration Examples.TrafficLight.Phase :=
  Graph.Enumeration.ofList [.stop, .go, .caution] (by intro s; cases s <;> simp)

theorem true_no_counterexample :
    (Examples.Checker.singleton.counterexample? Formula.truth
      Examples.Checker.singleton_serial unitOrder).isSome = false := by decide

theorem false_counterexample :
    (Examples.Checker.singleton.counterexample? .falsehood
      Examples.Checker.singleton_serial unitOrder).isSome = true := by
  unfold FiniteKripke.counterexample? FiniteKripke.acceptedLasso?
  rw [Graph.acceptingLasso?_eq_spec]
  decide

/-- Source labels are read at zero; p holds there even though it immediately disappears. -/
theorem initial_eventuality :
    (Examples.Checker.twoState false |>.counterexample? (◇ Examples.Checker.p)
      (Examples.Checker.twoState_serial false) boolOrder).isSome = false := by
  unfold FiniteKripke.counterexample? FiniteKripke.acceptedLasso?
  rw [Graph.acceptingLasso?_eq_spec]
  decide

theorem next_counterexample :
    (Examples.Checker.twoState false |>.counterexample? (𝒩 Examples.Checker.p)
      (Examples.Checker.twoState_serial false) boolOrder).isSome = true := by
  unfold FiniteKripke.counterexample? FiniteKripke.acceptedLasso?
  rw [Graph.acceptingLasso?_eq_spec]
  decide

theorem next_successor :
    (Examples.Checker.twoState false |>.counterexample? (𝒩 Examples.Checker.q)
      (Examples.Checker.twoState_serial false) boolOrder).isSome = false := by
  unfold FiniteKripke.counterexample? FiniteKripke.acceptedLasso?
  rw [Graph.acceptingLasso?_eq_spec]
  decide

/-- A small computed witness is connected to its own path by the generic theorem. -/
theorem extracted_false_trace :
    ∃ l, ∃ h : Examples.Checker.singleton.counterexample? .falsehood
        Examples.Checker.singleton_serial unitOrder = some l,
      let p := Examples.Checker.singleton.productLassoPath
        (Formula.falsehood : Formula Nat).violationAutomaton l
        (Examples.Checker.singleton.counterexample?_valid _ _ _ h)
      p.IsInitial ∧ ¬ WordSat p.word .falsehood := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp false_counterexample
  exact ⟨l, hl, Examples.Checker.singleton.counterexample?_sound _ _ _ hl⟩

/-- The generic lower layer also rejects an accepting deadlock. -/
theorem deadlock_no_lasso :
    (Examples.Checker.deadlock.acceptedLasso?
      (Formula.falsehood : Formula Nat).violationAutomaton unitOrder
      (Formula.neg (.falsehood : Formula Nat)).automatonOrder).isSome = false := by
  unfold FiniteKripke.acceptedLasso?
  rw [Graph.acceptingLasso?_eq_spec]
  decide

/-- Finite boundary validation for compiled execution tests; not a proof oracle. -/
def edgesValid {S : Type} [DecidableEq S] (successors : S → Finset S) (nodes : List S) : Bool :=
  (nodes.zip nodes.tail).all fun pair => decide (pair.2 ∈ successors pair.1)

def certificateValid {S : Type} [DecidableEq S] (seeds : Finset S)
    (successors : S → Finset S) (accepting : Finset S) (l : Graph.Lasso S) : Bool :=
  decide (l.sequence 0 ∈ seeds) &&
  edgesValid successors (l.prefix ++ [l.entry]) &&
  edgesValid successors (l.loop ++ [l.entry]) && decide (l.entry ∈ accepting)

@[noinline] def executeFormula {S AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (M : FiniteKripke S AP) (φ : Formula AP) (hs : M.toKripke.Serial)
    (order : Graph.Enumeration S) : IO (Option (Graph.Lasso (S × Formula.AutomatonState (.neg φ)))) :=
  pure (M.counterexample? φ hs order)

/-- Print the system view, without requiring Repr for internal tableau proof subtypes. -/
def report {S AP Q : Type} [Fintype S] [DecidableEq S] [Repr S]
    [Fintype Q] [DecidableEq Q] (name : String) (M : FiniteKripke S AP)
    (A : FiniteBuchi Q (Valuation AP)) (atoms : List AP)
    (result : Option (Graph.Lasso (S × Q))) (expected : Bool) (elapsed : Nat) : IO Unit := do
  unless result.isSome == expected do
    throw (IO.userError s!"{name}: expected witness {expected}, got {result.isSome}")
  IO.println s!"{name}: witness={result.isSome}, product={Fintype.card S * Fintype.card Q}, elapsed={elapsed} ms"
  if let some l := result then
    unless certificateValid (M.productInitials A) (M.productSuccessors A)
        (FiniteKripke.productAccepting A) l do
      throw (IO.userError s!"{name}: invalid finite lasso certificate")
    let view := l.map Prod.fst
    IO.println s!"  prefix ({view.prefix.length}): {repr view.prefix}"
    IO.println s!"  loop ({view.loop.length}), repeats forever: {repr view.loop}"
    IO.println s!"  prefix valuations: {repr (view.prefix.map fun s => atoms.map (M.label s))}"
    IO.println s!"  loop valuations: {repr (view.loop.map fun s => atoms.map (M.label s))}"

/-- Time the extraction itself; validation and rendering follow the timer. -/
def expectFormula {S AP : Type} [Fintype S] [DecidableEq S] [Repr S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (φ : Formula AP) (hs : M.toKripke.Serial)
    (order : Graph.Enumeration S) (atoms : List AP) (expected : Bool) : IO Unit := do
  let start ← IO.monoMsNow
  let result ← executeFormula M φ hs order
  let stop ← IO.monoMsNow
  report name M φ.violationAutomaton atoms result expected (stop - start)

namespace Lock
open Examples.TwoThreadLock

def pcOrder : Graph.Enumeration PC :=
  Graph.Enumeration.ofList [.idle, .trying, .checked, .critical] (by intro p; cases p <;> simp)
def stateOrder : Graph.Enumeration State :=
  Graph.Enumeration.ofList ((pcOrder.product (pcOrder.product boolOrder)).states.map
    fun p => (⟨p.1, p.2.1, p.2.2⟩ : State)) (by
      intro s
      exact List.mem_map.mpr ⟨(s.pc0, s.pc1, s.locked),
        (pcOrder.product (pcOrder.product boolOrder)).complete _, by cases s; rfl⟩)

/-- Once a collision has occurred, any infinite continuation witnesses failed safety. -/
def safetyViolation : FiniteBuchi Bool (Valuation Atom) :=
  Monitors.guessAndStay (fun v => v (.inCritical .zero) && v (.inCritical .one)) (fun _ => true)

theorem safetyViolation_accepts (word : Word Atom) :
    ωAcceptor.Accepts safetyViolation.toBuchi word ↔ ¬ WordSat word mutualExclusion := by
  classical
  rw [safetyViolation, Monitors.guessAndStay_accepts]
  simp [WordSat, mutualExclusion, critical, sat_globally, sat_conj, sat_neg, sat_atom]

/-- Any returned safety witness's own path violates mutual exclusion. -/
theorem extracted_safety_sound (M : FiniteKripke State Atom) {l : Graph.Lasso (State × Bool)}
    (h : M.acceptedLasso? safetyViolation stateOrder boolOrder = some l) :
    let p := M.productLassoPath safetyViolation l (M.acceptedLasso?_valid _ _ _ h).1
    p.IsInitial ∧ ¬ WordSat p.word mutualExclusion := by
  have hs := M.acceptedLasso?_sound safetyViolation stateOrder boolOrder h
  exact ⟨hs.1, (safetyViolation_accepts _).mp hs.2⟩

/-- Starvation is possible because scheduling is unconstrained, despite atomic safety. -/
theorem extracted_starvation_sound {l : Graph.Lasso (State × Bool)}
    (h : atomic.acceptedLasso? (Monitors.notResponse (.requesting .zero) (.inCritical .zero))
      stateOrder boolOrder = some l) :
    let p := atomic.productLassoPath _ l (atomic.acceptedLasso?_valid _ _ _ h).1
    p.IsInitial ∧ ¬ WordSat p.word (starvationFreedom .zero) := by
  have hs := atomic.acceptedLasso?_sound _ stateOrder boolOrder h
  exact ⟨hs.1, (Monitors.notResponse_accepts _ _ _).mp hs.2⟩

@[noinline] def executeMonitor (M : FiniteKripke State Atom)
    (A : FiniteBuchi Bool (Valuation Atom)) : IO (Option (Graph.Lasso (State × Bool))) :=
  pure (M.acceptedLasso? A stateOrder boolOrder)

def expect (name : String) (M : FiniteKripke State Atom)
    (A : FiniteBuchi Bool (Valuation Atom)) (expected : Bool) : IO Unit := do
  let start ← IO.monoMsNow
  let result ← executeMonitor M A
  let stop ← IO.monoMsNow
  report name M A [.inCritical .zero, .inCritical .one, .requesting .zero, .lockHeld]
    result expected (stop - start)

end Lock

def runExamples : IO Unit := do
  let atoms := [Examples.Buchi.requestAtom, Examples.Buchi.grantAtom]
  let eventualGrant : Formula Examples.RequestGrant.Atom := ◇ (.atom Examples.Buchi.grantAtom)
  expectFormula "request cycle/eventual grant" Examples.Buchi.cycleSystem eventualGrant
    Examples.Buchi.cycleSerial requestOrder atoms false
  expectFormula "waiting/eventual grant" Examples.Buchi.waitingSystem eventualGrant
    Examples.Buchi.waitingSerial requestOrder atoms true
  expectFormula "request cycle/response" Examples.Buchi.cycleSystem Examples.RequestGrant.response
    Examples.Buchi.cycleSerial requestOrder atoms false
  expectFormula "waiting/response" Examples.Buchi.waitingSystem Examples.RequestGrant.response
    Examples.Buchi.waitingSerial requestOrder atoms true
  let colours := [Examples.TrafficLight.Colour.red, .green, .yellow]
  expectFormula "traffic/eventual green" Examples.TrafficLight.controller Examples.TrafficLight.eventuallyGreen
    Examples.TrafficLight.controller_serial trafficOrder colours false
  expectFormula "stuck/eventual green" Examples.TrafficLight.stuckController Examples.TrafficLight.eventuallyGreen
    Examples.TrafficLight.stuckController_serial trafficOrder colours true
  expectFormula "traffic/red response" Examples.TrafficLight.controller Examples.TrafficLight.redResponds
    Examples.TrafficLight.controller_serial trafficOrder colours false
  expectFormula "stuck/red response" Examples.TrafficLight.stuckController Examples.TrafficLight.redResponds
    Examples.TrafficLight.stuckController_serial trafficOrder colours true
  Lock.expect "broken lock/mutual exclusion" Examples.TwoThreadLock.broken Lock.safetyViolation true
  Lock.expect "atomic lock/mutual exclusion" Examples.TwoThreadLock.atomic Lock.safetyViolation false
  Lock.expect "atomic lock/starvation" Examples.TwoThreadLock.atomic
    (Monitors.notResponse (.requesting .zero) (.inCritical .zero)) true

#eval runExamples
end Examples.Counterexample
