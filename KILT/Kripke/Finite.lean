import KILT.Kripke.Semantics
import KILT.Graph.Routes

/-!
# Executable finite Kripke structures

`FiniteKripke` stores initial states and successors as finite sets. Its
`toKripke` adapter is the semantic contract: algorithms compute with the
finite data, while existing paths and LTL satisfaction remain unchanged.
Deadlocks are reported rather than repaired by implicit self-loops.
-/

namespace KILT

universe u v

/-- Executable finite transition-system data. Atomic proposition identifiers
remain unrestricted; only the state carrier must be finite and decidable. -/
structure FiniteKripke (State : Type u) (AP : Type v)
    [Fintype State] [DecidableEq State] where
  initials : Finset State
  initials_nonempty : initials.Nonempty
  successors : State → Finset State
  label : State → LTL.Valuation AP

namespace FiniteKripke

variable {State : Type u} {AP : Type v}
variable [Fintype State] [DecidableEq State]

/-- Forget executable storage while preserving the relational semantics. -/
def toKripke (M : FiniteKripke State AP) : Kripke State AP where
  initial state := state ∈ M.initials
  initial_nonempty := M.initials_nonempty
  step source target := target ∈ M.successors source
  label := M.label

@[simp] theorem toKripke_initial (M : FiniteKripke State AP) (state : State) :
    M.toKripke.initial state ↔ state ∈ M.initials := Iff.rfl

@[simp] theorem toKripke_step (M : FiniteKripke State AP)
    (source target : State) :
    M.toKripke.step source target ↔ target ∈ M.successors source := Iff.rfl

@[simp] theorem toKripke_label (M : FiniteKripke State AP) (state : State) :
    M.toKripke.label state = M.label state := rfl

/-- All states reachable by a finite route from an initial state. -/
def reachableSet (M : FiniteKripke State AP) : Finset State :=
  Graph.reachableSet M.initials M.successors

/-- Mathematical reachability used by the correctness statement. -/
def Reachable (M : FiniteKripke State AP) (state : State) : Prop :=
  Graph.Reachable M.initials M.successors state

@[simp] theorem mem_reachableSet_iff (M : FiniteKripke State AP)
    (state : State) :
    state ∈ M.reachableSet ↔ M.Reachable state :=
  Graph.mem_reachableSet_iff

/-- Executable route lookup using an explicit traversal order. -/
def route? (M : FiniteKripke State AP) (order : Graph.Enumeration State)
    (target : State) : Option (List State) :=
  Graph.route? order M.initials M.successors target

@[simp] theorem route?_isSome_iff (M : FiniteKripke State AP)
    (order : Graph.Enumeration State) (target : State) :
    (M.route? order target).isSome = true ↔ M.Reachable target :=
  Graph.route?_isSome_iff order M.initials M.successors target

theorem route?_sound (M : FiniteKripke State AP)
    (order : Graph.Enumeration State) {target : State} {nodes : List State}
    (hroute : M.route? order target = some nodes) :
    ∃ source ∈ M.initials,
      nodes.IsChainFromTo (Graph.Step M.successors) source target :=
  Graph.route?_sound order M.initials M.successors hroute

/-- Every state with no outgoing transition. -/
def deadlocks (M : FiniteKripke State AP) : Finset State :=
  Finset.univ.filter fun state => M.successors state = ∅

/-- Deadlocks that can be reached from an initial state. -/
def reachableDeadlocks (M : FiniteKripke State AP) : Finset State :=
  M.reachableSet.filter fun state => M.successors state = ∅

/-- Boolean global seriality check. -/
def isSerial (M : FiniteKripke State AP) : Bool := decide (M.deadlocks = ∅)

/-- Boolean diagnostic for reachable deadlocks. -/
def hasNoReachableDeadlocks (M : FiniteKripke State AP) : Bool :=
  decide (M.reachableDeadlocks = ∅)

@[simp] theorem mem_deadlocks_iff (M : FiniteKripke State AP) (state : State) :
    state ∈ M.deadlocks ↔ M.successors state = ∅ := by
  simp [deadlocks]

@[simp] theorem mem_reachableDeadlocks_iff (M : FiniteKripke State AP)
    (state : State) :
    state ∈ M.reachableDeadlocks ↔
      state ∈ M.reachableSet ∧ M.successors state = ∅ := by
  simp [reachableDeadlocks]

/-- The executable global check is exactly the existing semantic seriality
predicate. -/
theorem isSerial_eq_true_iff (M : FiniteKripke State AP) :
    M.isSerial = true ↔ M.toKripke.Serial := by
  constructor
  · intro hserial state
    have hempty : M.deadlocks = ∅ := decide_eq_true_iff.mp hserial
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hdeadlock
    have hmem : state ∈ M.deadlocks := (M.mem_deadlocks_iff state).mpr hdeadlock
    rw [hempty] at hmem
    simp at hmem
  · intro hserial
    apply decide_eq_true
    ext state
    simp only [M.mem_deadlocks_iff state, Finset.notMem_empty, iff_false]
    intro hdeadlock
    rcases hserial state with ⟨target, htarget⟩
    change target ∈ M.successors state at htarget
    simp [hdeadlock] at htarget

/-- Reachable-deadlock absence means precisely that every reachable state has
an outgoing transition. -/
theorem hasNoReachableDeadlocks_eq_true_iff (M : FiniteKripke State AP) :
    M.hasNoReachableDeadlocks = true ↔
      ∀ state, state ∈ M.reachableSet → (M.successors state).Nonempty := by
  constructor
  · intro hnone state hreachable
    have hempty : M.reachableDeadlocks = ∅ := decide_eq_true_iff.mp hnone
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hdeadlock
    have hmem : state ∈ M.reachableDeadlocks :=
      (M.mem_reachableDeadlocks_iff state).mpr ⟨hreachable, hdeadlock⟩
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    apply decide_eq_true
    ext state
    simp only [M.mem_reachableDeadlocks_iff state, Finset.notMem_empty,
      iff_false]
    intro hdeadlock
    have hsuccessor := hnone state hdeadlock.1
    rw [hdeadlock.2] at hsuccessor
    exact Finset.not_nonempty_empty hsuccessor

/-- Every position on an initial infinite path is in the finite reachable set. -/
theorem path_state_mem_reachableSet (M : FiniteKripke State AP)
    (path : M.toKripke.Path) (hinitial : path.IsInitial) (index : Nat) :
    path.states index ∈ M.reachableSet := by
  apply (M.mem_reachableSet_iff (path.states index)).mpr
  induction index with
  | zero =>
      exact ⟨path.states 0, hinitial, Relation.ReflTransGen.refl⟩
  | succ index ih =>
      rcases ih with ⟨source, hsource, hreach⟩
      have hedge := path.valid index
      change path.states (index + 1) ∈ M.successors (path.states index) at hedge
      exact ⟨source, hsource, hreach.tail hedge⟩

end FiniteKripke

end KILT
