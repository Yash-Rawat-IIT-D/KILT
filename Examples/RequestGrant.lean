import KILT
import Examples.Syntax

/-!
# Request/grant Kripke examples

This module will contain a small serial request/grant system, a property true
on every initial path, and an explicit violating path.  It will also document
the absence of fairness assumptions in the initial model.
-/

namespace Examples.RequestGrant

open KILT KILT.LTL KILT.Kripke
open scoped KILT.LTL

abbrev Atom := Syntax.Atom

def request : Formula Atom := Syntax.request
def grant : Formula Atom := Syntax.grant

def response : Formula Atom := □ (request ⟹ ◇ grant)

inductive State where
  | waiting
  | granting
  deriving DecidableEq, Repr

instance : Fintype State where
  elems := {.waiting, .granting}
  complete state := by cases state <;> simp

/-- Waiting exposes `request`; granting exposes `grant`. -/
def stateLabel : State → Valuation Atom
  | .waiting => fun atom => match atom with
    | .request => true
    | .grant => false
  | .granting => fun atom => match atom with
    | .request => false
    | .grant => true

def cycleStep : State → State → Prop
  | .waiting, .granting => True
  | .granting, .waiting => True
  | _, _ => False

/-- The positive system must alternate between waiting and granting. -/
def cycleModel : KILT.Kripke State Atom where
  initial s := s = .waiting
  initial_nonempty := ⟨.waiting, rfl⟩
  step := cycleStep
  label := stateLabel

theorem cycle_serial : cycleModel.Serial := by
  intro s
  cases s with
  | waiting => exact ⟨.granting, trivial⟩
  | granting => exact ⟨.waiting, trivial⟩

/-- The deterministic next-state function is used only to give a concrete
path for indexing and suffix examples. -/
def advance : State → State
  | .waiting => .granting
  | .granting => .waiting

def cyclePath : cycleModel.Path where
  states := Cslib.ωSequence.iterate advance .waiting
  valid := by
    intro i
    rw [show i + 1 = Nat.succ i by omega,
      Cslib.ωSequence.get_succ_iterate']
    cases Cslib.ωSequence.iterate advance State.waiting i <;> trivial

theorem cyclePath_initial : cyclePath.IsInitial := rfl

/-- Position zero observes the label of the initial waiting state. -/
example : cyclePath.word 0 Syntax.Atom.request = true := rfl

/-- Dropping a step preserves validity because the result is still a `Path`. -/
example : ∀ i, cycleModel.step ((cyclePath.drop 1).states i)
    ((cyclePath.drop 1).states (i + 1)) := (cyclePath.drop 1).valid

/-- The one-step suffix begins in granting, which is not an initial state. -/
theorem cyclePath_drop_one_not_initial : ¬ (cyclePath.drop 1).IsInitial := by
  intro h
  change (cyclePath.drop 1).states 0 = State.waiting at h
  have hgranting : (cyclePath.drop 1).states 0 = State.granting := rfl
  rw [hgranting] at h
  cases h

/-- Path suffixes and indexed LTL evaluation use the same offset. -/
example (formula : Formula Atom) :
    WordSat (cyclePath.drop 1).word formula ↔ Sat cyclePath.word 1 formula :=
  cyclePath.wordSat_drop 1 formula

/-- Every request in the alternating system is followed by a grant at the
next position. -/
theorem cycle_satisfies_response : cycleModel.Satisfies response := by
  intro p _
  apply sat_globally.mpr
  intro i _
  apply sat_imp.mpr
  intro hrequest
  apply sat_eventually.mpr
  refine ⟨i + 1, by omega, ?_⟩
  change stateLabel (p.states (i + 1)) Syntax.Atom.grant = true
  have hstep := p.valid i
  change cycleStep (p.states i) (p.states (i + 1)) at hstep
  change stateLabel (p.states i) Syntax.Atom.request = true at hrequest
  cases hcurrent : p.states i with
  | waiting =>
      rw [hcurrent] at hstep
      cases hnext : p.states (i + 1) with
      | waiting =>
          rw [hnext] at hstep
          exact False.elim hstep
      | granting =>
          rfl
  | granting =>
      rw [hcurrent] at hrequest
      cases hrequest

/-- The negative variant permits a request to wait forever. -/
def waitingStep : State → State → Prop
  | .waiting, .waiting => True
  | .waiting, .granting => True
  | .granting, .waiting => True
  | _, _ => False

def waitingModel : KILT.Kripke State Atom where
  initial s := s = .waiting
  initial_nonempty := ⟨.waiting, rfl⟩
  step := waitingStep
  label := stateLabel

theorem waiting_serial : waitingModel.Serial := by
  intro s
  cases s with
  | waiting => exact ⟨.waiting, trivial⟩
  | granting => exact ⟨.waiting, trivial⟩

def stalledPath : waitingModel.Path where
  states := Cslib.ωSequence.const .waiting
  valid := fun _ => trivial

theorem stalledPath_initial : stalledPath.IsInitial := rfl

theorem stalledPath_refutes_response : ¬ WordSat stalledPath.word response := by
  intro hresponse
  have hatZero := sat_globally.mp hresponse 0 (Nat.le_refl 0)
  have heventually := sat_imp.mp hatZero
    (show Sat stalledPath.word 0 request from rfl)
  rcases sat_eventually.mp heventually with ⟨j, _, hgrant⟩
  change stateLabel (stalledPath.states j) Syntax.Atom.grant = true at hgrant
  cases hgrant

/-- With no fairness assumption, the permanent-waiting execution refutes the
system property even though a granting transition is always available. -/
theorem waiting_does_not_satisfy_response :
    ¬ waitingModel.Satisfies response := by
  intro hsatisfies
  exact stalledPath_refutes_response (hsatisfies stalledPath stalledPath_initial)

/-- A nonempty-initial model may still have no infinite path when its initial
state deadlocks. -/
def deadlockModel : KILT.Kripke Unit Atom where
  initial _ := True
  initial_nonempty := ⟨(), trivial⟩
  step _ _ := False
  label _ _ := false

theorem deadlock_has_no_path : ¬ Nonempty deadlockModel.Path := by
  rintro ⟨p⟩
  exact p.valid 0

/-- Universal infinite-path satisfaction is consequently vacuous here. -/
theorem deadlock_satisfies_vacuously (formula : Formula Atom) :
    deadlockModel.Satisfies formula := by
  intro p _
  exact (deadlock_has_no_path ⟨p⟩).elim

/-- This word intentionally disagrees with the request label at position zero. -/
def wrongWord : Word Atom := Cslib.ωSequence.const (fun _ => false)

theorem wrong_labels_are_not_a_run :
    ¬ cycleModel.toNA.Run wrongWord cyclePath.states := by
  intro run
  have hword := (toNA_run_iff cycleModel wrongWord cyclePath.states).mp run |>.2.2
  have hatZero := congrArg (fun word : Word Atom => word 0 Syntax.Atom.request) hword
  cases hatZero

end Examples.RequestGrant

#print axioms KILT.Kripke.Path.wordSat_drop
#print axioms KILT.Kripke.satisfies_iff_all_runs
#print axioms Examples.RequestGrant.cycle_satisfies_response
#print axioms Examples.RequestGrant.waiting_does_not_satisfy_response
#print axioms Examples.RequestGrant.deadlock_satisfies_vacuously
#print axioms Examples.RequestGrant.wrong_labels_are_not_a_run
