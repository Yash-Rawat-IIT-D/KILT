import KILT
import Examples.Theory.Syntax

/-!
# Request/grant: progress, infinite waiting and deadlock

Start with two observable propositions and a system that alternates between
requesting and granting. Then add a waiting self-loop: a grant remains
available, but one valid execution never takes it. The same response formula
therefore distinguishes guaranteed progress from mere reachability.

These examples use the general `Kripke` and `Path` interfaces to prove facts
directly from trace semantics. The final examples explain why initial states,
seriality and matching state labels are separate requirements. For a shorter
user session with finite-model checking and `kilt_verify`, see
`Examples/Demos/Frontend.lean`.
-/

namespace Examples.RequestGrant

open KILT KILT.LTL KILT.Kripke
open scoped KILT.LTL

/-! ## Propositions and the alternating system -/

/-- Reuse the request/grant proposition names from the syntax examples. -/
abbrev Atom := Syntax.Atom

/-- The request observation, lifted to a formula for use in temporal properties. -/
def request : Formula Atom := Syntax.request
/-- The grant observation, used as the eventual goal of a request. -/
def grant : Formula Atom := Syntax.grant

/-- At every position, a request must be granted now or later; no timeout is specified. -/
def response : Formula Atom := □ (request ⟹ ◇ grant)

/-- Distinguish a pending request from a grant. Equality supports finite sets;
`Repr` makes states readable when displayed. -/
inductive State where
  | waiting
  | granting
  deriving DecidableEq, Repr

/-- Enumerate the whole carrier; `complete` certifies that neither state is omitted. -/
instance : Fintype State where
  elems := {.waiting, .granting}
  complete state := by cases state <;> simp

/-- Translate internal states to the truth values observed by LTL formulas:
waiting makes only `request` true, and granting makes only `grant` true. -/
def stateLabel : State → Valuation Atom
  | .waiting => fun atom => match atom with
    | .request => true
    | .grant => false
  | .granting => fun atom => match atom with
    | .request => false
    | .grant => true

/-- Permit exactly the two alternating edges, so a request cannot keep waiting. -/
def cycleStep : State → State → Prop
  | .waiting, .granting => True
  | .granting, .waiting => True
  | _, _ => False

/-- Start in waiting and use `cycleStep` for allowed moves. The initial witness
certifies a starting state exists; `stateLabel` supplies its observations. -/
def cycleModel : KILT.Kripke State Atom where
  initial s := s = .waiting
  initial_nonempty := ⟨.waiting, rfl⟩
  step := cycleStep
  label := stateLabel

/-- Choose a legal successor for each state: the no-deadlock certificate. -/
theorem cycle_serial : cycleModel.Serial := by
  intro s
  cases s with
  | waiting => exact ⟨.granting, trivial⟩
  | granting => exact ⟨.waiting, trivial⟩

/-! ## Reading one execution, then proving the property for every execution -/

/-- A next-state function makes the alternating trace easy to construct by
iteration; universal satisfaction is proved separately below. -/
def advance : State → State
  | .waiting => .granting
  | .granting => .waiting

/-- Package the infinite state sequence with `valid`, a proof that every
adjacent pair follows an allowed edge. This is one execution of the model. -/
def cyclePath : cycleModel.Path where
  states := Cslib.ωSequence.iterate advance .waiting
  valid := by
    intro i
    rw [show i + 1 = Nat.succ i by omega,
      Cslib.ωSequence.get_succ_iterate']
    cases Cslib.ωSequence.iterate advance State.waiting i <;> trivial

/-- The constructed execution starts in the model's declared initial state. -/
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

/-! ## An available grant need not be taken -/

/-- Add waiting → waiting while keeping the grant edge available. Without
fairness, this extra choice permits indefinite postponement. -/
def waitingStep : State → State → Prop
  | .waiting, .waiting => True
  | .waiting, .granting => True
  | .granting, .waiting => True
  | _, _ => False

/-- Keep the initial state and labels unchanged, isolating the effect of the
extra transition on the same response property. -/
def waitingModel : KILT.Kripke State Atom where
  initial s := s = .waiting
  initial_nonempty := ⟨.waiting, rfl⟩
  step := waitingStep
  label := stateLabel

/-- This system also has no deadlocks; seriality alone does not force a grant. -/
theorem waiting_serial : waitingModel.Serial := by
  intro s
  cases s with
  | waiting => exact ⟨.waiting, trivial⟩
  | granting => exact ⟨.waiting, trivial⟩

/-- Repeat waiting forever along its real self-loop to construct a violating
infinite execution, rather than merely a long finite wait. -/
def stalledPath : waitingModel.Path where
  states := Cslib.ωSequence.const .waiting
  valid := fun _ => trivial

/-- The stalling execution is eligible for the model's initial-path semantics. -/
theorem stalledPath_initial : stalledPath.IsInitial := rfl

/-- A request holds at position zero, but no future position supplies its grant. -/
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

/-! ## Why a starting state is not enough -/

/-- Use `Unit` for one initial state and give it no outgoing edges. This
separates nonempty initials from the requirement of infinite continuation. -/
def deadlockModel : KILT.Kripke Unit Atom where
  initial _ := True
  initial_nonempty := ⟨(), trivial⟩
  step _ _ := False
  label _ _ := false

/-- Even the first step of a `Path` would require an edge this model lacks. -/
theorem deadlock_has_no_path : ¬ Nonempty deadlockModel.Path := by
  rintro ⟨p⟩
  exact p.valid 0

/-- Every formula holds vacuously because there are no infinite paths. This
explains why the public checker asks separately for a seriality proof. -/
theorem deadlock_satisfies_vacuously (formula : Formula Atom) :
    deadlockModel.Satisfies formula := by
  intro p _
  exact (deadlock_has_no_path ⟨p⟩).elim

/-! ## Automaton runs must observe the model's labels -/

/-- Make every proposition false to deliberately disagree with the initial
waiting state's request label. This tests the word/run correspondence. -/
def wrongWord : Word Atom := Cslib.ωSequence.const (fun _ => false)

/-- Legal state edges alone do not give an automaton run: the supplied word
must also agree with the labels of that same execution. -/
theorem wrong_labels_are_not_a_run :
    ¬ cycleModel.toNA.Run wrongWord cyclePath.states := by
  intro run
  have hword := (toNA_run_iff cycleModel wrongWord cyclePath.states).mp run |>.2.2
  have hatZero := congrArg (fun word : Word Atom => word 0 Syntax.Atom.request) hword
  cases hatZero

end Examples.RequestGrant

-- Inspect proof dependencies for the semantic bridges and representative results.
#print axioms KILT.Kripke.Path.wordSat_drop
#print axioms KILT.Kripke.satisfies_iff_all_runs
#print axioms Examples.RequestGrant.cycle_satisfies_response
#print axioms Examples.RequestGrant.waiting_does_not_satisfy_response
#print axioms Examples.RequestGrant.deadlock_satisfies_vacuously
#print axioms Examples.RequestGrant.wrong_labels_are_not_a_run
