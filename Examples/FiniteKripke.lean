import Examples.RequestGrant

/-!
# Finite Kripke and reachability examples

These examples exercise the executable graph layer independently of temporal
logic, then show that finite request/grant data has exactly the relational
semantics proved in `Examples.RequestGrant`.
-/

namespace Examples.FiniteKripke

open KILT

inductive Node where
  | start
  | left
  | right
  | merge
  | loop
  | dead
  | isolated
  deriving DecidableEq, Repr

instance : Fintype Node where
  elems := {.start, .left, .right, .merge, .loop, .dead, .isolated}
  complete state := by cases state <;> simp

def successors : Node → Finset Node
  | .start => {.left, .right}
  | .left => {.merge}
  | .right => {.merge, .dead}
  | .merge => {.loop}
  | .loop => {.loop}
  | .dead => ∅
  | .isolated => ∅

def label : Node → LTL.Valuation Nat
  | .start => fun atom => atom == 0
  | .left => fun atom => atom == 1
  | .right => fun atom => atom == 2
  | .merge => fun atom => atom == 3
  | .loop => fun atom => atom == 4
  | .dead => fun atom => atom == 5
  | .isolated => fun atom => atom == 6

/-- This model deliberately uses `Nat` atoms: only states need to be finite. -/
def model : FiniteKripke Node Nat where
  initials := {.start}
  initials_nonempty := ⟨.start, by simp⟩
  successors := successors
  label := label

def leftFirst : Graph.Enumeration Node where
  states := [.start, .left, .right, .merge, .loop, .dead, .isolated]
  nodup := by decide
  complete state := by cases state <;> simp

def rightFirst : Graph.Enumeration Node where
  states := [.start, .right, .left, .merge, .loop, .dead, .isolated]
  nodup := by decide
  complete state := by cases state <;> simp

/-- Empty generic seed sets discover no states. -/
example : Graph.reachableSet (∅ : Finset Node) successors = ∅ := by simp

/-- Branches merge, the self-loop remains reachable, and the disconnected
deadlock does not become reachable. -/
example : model.reachableSet =
    {.start, .left, .right, .merge, .loop, .dead} := by native_decide

example : model.deadlocks = {.dead, .isolated} := by native_decide
example : model.reachableDeadlocks = {.dead} := by native_decide
example : model.isSerial = false := by native_decide
example : model.hasNoReachableDeadlocks = false := by native_decide

/-- Both explicit orders find a valid witness, but select different branches. -/
example : model.route? leftFirst .merge =
    some [.start, .left, .merge] := by native_decide

example : model.route? rightFirst .merge =
    some [.start, .right, .merge] := by native_decide

example : (model.route? leftFirst .merge).isSome =
    (model.route? rightFirst .merge).isSome := by native_decide

/-- A second initial state is included by zero-step reachability even when it
has no outgoing transition. -/
def multipleInitials : FiniteKripke Node Nat where
  initials := {.start, .isolated}
  initials_nonempty := ⟨.start, by simp⟩
  successors := successors
  label := label

example : .isolated ∈ multipleInitials.reachableSet := by native_decide
example : multipleInitials.route? leftFirst .isolated =
    some [.isolated] := by native_decide

/-- The one-state deadlock has a zero-step finite route, although its
relational adapter has no infinite path. -/
def deadlockFinite : FiniteKripke Unit Examples.RequestGrant.Atom where
  initials := {()}
  initials_nonempty := ⟨(), by simp⟩
  successors _ := ∅
  label _ _ := false

def unitOrder : Graph.Enumeration Unit where
  states := [()]
  nodup := by simp
  complete state := by cases state; simp

example : deadlockFinite.reachableSet = {()} := by native_decide
example : deadlockFinite.route? unitOrder () = some [()] := by native_decide

namespace RequestGrant

open Examples.RequestGrant

def cycleFinite : FiniteKripke State Atom where
  initials := {.waiting}
  initials_nonempty := ⟨.waiting, by simp⟩
  successors
    | .waiting => {.granting}
    | .granting => {.waiting}
  label := stateLabel

def waitingFinite : FiniteKripke State Atom where
  initials := {.waiting}
  initials_nonempty := ⟨.waiting, by simp⟩
  successors
    | .waiting => {.waiting, .granting}
    | .granting => {.waiting}
  label := stateLabel

/-- The finite adapter preserves the positive system exactly. -/
theorem cycle_toKripke : cycleFinite.toKripke = cycleModel := by
  rw [KILT.Kripke.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext state
    apply propext
    cases state <;> simp [cycleFinite, cycleModel]
  · funext source target
    apply propext
    cases source <;> cases target <;> simp [cycleFinite, cycleModel, cycleStep]

/-- The finite adapter also preserves the waiting-loop counterexample model. -/
theorem waiting_toKripke : waitingFinite.toKripke = waitingModel := by
  rw [KILT.Kripke.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext state
    apply propext
    cases state <;> simp [waitingFinite, waitingModel]
  · funext source target
    apply propext
    cases source <;> cases target <;>
      simp [waitingFinite, waitingModel, waitingStep]

example : cycleFinite.isSerial = true := by native_decide
example : cycleFinite.reachableDeadlocks = ∅ := by native_decide
example : waitingFinite.isSerial = true := by native_decide
example : waitingFinite.reachableDeadlocks = ∅ := by native_decide

theorem deadlock_toKripke : deadlockFinite.toKripke = deadlockModel := by
  rw [KILT.Kripke.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · funext state
    apply propext
    cases state
    simp [deadlockFinite, deadlockModel]
  · funext source target
    apply propext
    cases source
    cases target
    simp [deadlockFinite, deadlockModel]

/-- Existing temporal proofs transfer across the finite adapter; they are not
reproved by inspecting the executable graph. -/
theorem cycle_satisfies_response :
    cycleFinite.toKripke.Satisfies response := by
  rw [cycle_toKripke]
  exact Examples.RequestGrant.cycle_satisfies_response

theorem waiting_refutes_response :
    ¬ waitingFinite.toKripke.Satisfies response := by
  rw [waiting_toKripke]
  exact Examples.RequestGrant.waiting_does_not_satisfy_response

theorem deadlock_has_no_infinite_path :
    ¬ Nonempty deadlockFinite.toKripke.Path := by
  rw [deadlock_toKripke]
  exact Examples.RequestGrant.deadlock_has_no_path

theorem deadlock_satisfies_vacuously (formula : LTL.Formula Atom) :
    deadlockFinite.toKripke.Satisfies formula := by
  rw [deadlock_toKripke]
  exact Examples.RequestGrant.deadlock_satisfies_vacuously formula

end RequestGrant

end Examples.FiniteKripke

#eval Examples.FiniteKripke.model.route?
  Examples.FiniteKripke.leftFirst .merge
#eval Examples.FiniteKripke.model.route?
  Examples.FiniteKripke.rightFirst .merge
#eval Examples.FiniteKripke.model.isSerial
#eval Examples.FiniteKripke.model.hasNoReachableDeadlocks

#print axioms KILT.Graph.mem_reachableSet_iff
#print axioms KILT.Graph.layers_stable_at_card
#print axioms KILT.Graph.routeTables_isSome_iff_mem_layers
#print axioms KILT.Graph.route?_sound
#print axioms KILT.Graph.route?_isSome_iff
#print axioms KILT.Graph.route_order_independent
#print axioms KILT.FiniteKripke.isSerial_eq_true_iff
#print axioms KILT.FiniteKripke.hasNoReachableDeadlocks_eq_true_iff
#print axioms KILT.FiniteKripke.path_state_mem_reachableSet
#print axioms Examples.FiniteKripke.RequestGrant.cycle_toKripke
#print axioms Examples.FiniteKripke.RequestGrant.cycle_satisfies_response
#print axioms Examples.FiniteKripke.RequestGrant.waiting_refutes_response
#print axioms Examples.FiniteKripke.RequestGrant.deadlock_satisfies_vacuously
