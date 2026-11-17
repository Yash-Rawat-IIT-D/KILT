import KILT.Automata.Product
import KILT.Automata.Monitors

/-!
# A traffic light, from observations to verified verdicts

Read top to bottom: observable colours → state labels → finite controller
→ formulas → paths and semantic proofs → finite graph queries and verdicts.

One step is a logical tick, not a measured duration. This is a single light:
red -> green -> yellow -> red. The faulty version may stay red forever.
Both keep exactly one colour lit; only the first guarantees progress.

The `FiniteKripke` declarations show the data a user supplies: initial states,
successors and labels. `Serial` proofs certify that execution can continue.
This file deliberately supplies violation monitors to `checkAgainst`, then
uses their language theorems to recover LTL statements. For formula-input
checking and the shorter proof frontend, see `Examples/Demos/Frontend.lean`.
The final `#eval` commands display executions and verdicts; the named theorems
provide the proofs.
-/

namespace Examples.TrafficLight

open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL

/-! ## Model data: observations, states and transitions -/

/-- Proposition names for LTL observations. Decidable equality lets labels
compare colours; `Repr` supports readable output. -/
inductive Colour where
  | red | green | yellow
  deriving DecidableEq, Repr

/-- Internal phases choose transitions; `label` below translates them into
colour observations. Keeping these roles separate makes the model explicit. -/
inductive Phase where
  | stop | go | caution
  deriving DecidableEq, Repr

/-- Give finite algorithms all three phases; `complete` checks none is missing. -/
instance : Fintype Phase where
  elems := {.stop, .go, .caution}
  complete phase := by cases phase <;> simp

/-- Convert a phase into the truth value of each colour proposition. For
example, `label .stop .red = true`, while its other colours are false. -/
def label : Phase → Valuation Colour
  | .stop => fun colour => colour == .red
  | .go => fun colour => colour == .green
  | .caution => fun colour => colour == .yellow

/-- Specify the normal cycle once, then reuse it for successors and traces. -/
def nextPhase : Phase → Phase
  | .stop => .go
  | .go => .caution
  | .caution => .stop

/-- A finite model starts at `stop`, advances to its singleton successor set,
and exposes `label`. The nonempty-initial proof certifies a starting point. -/
def controller : FiniteKripke Phase Colour where
  initials := {.stop}
  initials_nonempty := by simp
  successors phase := {nextPhase phase}
  label := label

/-- An extra red self-loop permits indefinite waiting, without a deadlock.
No fairness assumption forces the controller eventually to leave that loop. -/
def stuckController : FiniteKripke Phase Colour where
  initials := controller.initials
  initials_nonempty := controller.initials_nonempty
  successors phase := if phase = .stop then {.stop, .go} else {nextPhase phase}
  label := label

/-- Convert the computed no-deadlock test into the seriality proof required
by checking APIs; `decide` discharges this finite test. -/
theorem controller_serial : controller.toKripke.Serial :=
  controller.isSerial_eq_true_iff.mp (by decide)

/-- The red self-loop preserves seriality, although it can prevent progress. -/
theorem stuckController_serial : stuckController.toKripke.Serial :=
  stuckController.isSerial_eq_true_iff.mp (by decide)

/-! ## Writing safety, progress and next-step properties -/

/-- Lift the red proposition into formula syntax so temporal operators can use it. -/
def red : Formula Colour := .atom .red
/-- Formula observing the green label, used as the progress goal below. -/
def green : Formula Colour := .atom .green
/-- Formula observing yellow, completing the three-colour specifications. -/
def yellow : Formula Colour := .atom .yellow

/-- A single-position condition: at least one colour and no pair lit together.
The global operator in `safety` turns this into an invariant. -/
def oneColour : Formula Colour :=
  (red ∨ₗ green ∨ₗ yellow) ∧ₗ
  ¬ₗ (red ∧ₗ green) ∧ₗ ¬ₗ (red ∧ₗ yellow) ∧ₗ ¬ₗ (green ∧ₗ yellow)

/-- Exactly one colour must be lit at every position. Model satisfaction
requires this formula on every initial execution. -/
def safety : Formula Colour := □ oneColour
/-- Green must occur at some position, possibly the current one. -/
def eventuallyGreen : Formula Colour := ◇ green
/-- Every red observation creates an obligation to observe green eventually. -/
def redResponds : Formula Colour := □ (red ⟹ ◇ green)
/-- Require the next colour immediately at each tick, a stronger demand than
merely reaching it eventually. -/
def orderedColours : Formula Colour :=
  □ ((red ⟹ 𝒩 green) ∧ₗ (green ⟹ 𝒩 yellow) ∧ₗ (yellow ⟹ 𝒩 red))

/-! ## From one state trace to its word, then to universal proofs -/

/-- Construct `stop, go, caution, stop, ...` by iterating the transition rule;
this gives concrete positions for inspecting the temporal operators. -/
def phaseAt : Nat → Phase
  | 0 => .stop
  | n + 1 => nextPhase (phaseAt n)

/-- Attach a proof of every consecutive transition to `phaseAt`, making it a
model execution whose labels KILT can read as an infinite word. -/
def cyclePath : controller.toKripke.Path where
  states := ⟨phaseAt⟩
  valid i := by
    change phaseAt (i + 1) ∈ controller.successors (phaseAt i)
    simp [controller, phaseAt]

/-- Certify that this execution starts at `stop`, the sole initial phase. -/
theorem cyclePath_initial : cyclePath.IsInitial := by
  change Phase.stop ∈ ({.stop} : Finset Phase)
  decide

-- A state path becomes a valuation word by applying the label at each index.
example : cyclePath.word 0 .red = true := rfl
example : cyclePath.word 1 .green = true := rfl
example : cyclePath.word 2 .yellow = true := rfl
example : cyclePath.word 3 .red = true := rfl
example : WordSat cyclePath.word (𝒩 green) := rfl

/-- Red need not hold at the position where green first holds. -/
theorem red_until_green : WordSat cyclePath.word (red 𝒰 green) := by
  refine ⟨1, by decide, rfl, ?_⟩
  intro k _ hk
  have : k = 0 := by omega
  subst k
  rfl

/-- Release still requires its right operand at the release position.
At position 1 green holds but red does not, so `green R red` fails. -/
theorem not_green_release_red :
    ¬ WordSat cyclePath.word (Formula.release green red) := by
  intro h
  have hred := (sat_release.mp h) 1 (by decide) (by
    intro k _ hk
    have : k = 0 := by omega
    subst k
    simp [cyclePath, Kripke.Path.word, phaseAt, controller, label, green])
  change false = true at hred
  cases hred

-- Suffixes preserve transitions and observations, but need not start initially.
example : ¬ (cyclePath.drop 1).IsInitial := by
  change Phase.go ∉ ({.stop} : Finset Phase)
  decide
example : (cyclePath.drop 1).word = cyclePath.word.drop 1 := cyclePath.word_drop 1
example : WordSat (cyclePath.drop 1).word green ↔ Sat cyclePath.word 1 green :=
  cyclePath.wordSat_drop 1 green

/-- A snapshot invariant, independent of reachability or transition choices. -/
theorem label_oneColour (phase : Phase) :
    WordSat (Cslib.ωSequence.const (label phase)) oneColour := by
  cases phase <;> simp [oneColour, red, green, yellow, label]

/-- Every path has one colour at every position. This is a direct semantic
proof, not a call to a general formula checker. -/
theorem controller_safe : controller.toKripke.Satisfies safety := by
  intro path _
  apply sat_globally.mpr
  intro i _
  have h := label_oneColour (path.states i)
  exact h

/-- The same label invariant proves safety even when red may repeat forever. -/
theorem stuckController_safe : stuckController.toKripke.Satisfies safety := by
  intro path _
  apply sat_globally.mpr
  intro i _
  exact label_oneColour (path.states i)

/-- The transition relation enforces the next-colour formula on every path. -/
theorem controller_ordered : controller.toKripke.Satisfies orderedColours := by
  intro path _
  apply sat_globally.mpr
  intro i _
  have hedge := path.valid i
  change path.states (i + 1) ∈ controller.successors (path.states i) at hedge
  have hnext : path.states (i + 1) = nextPhase (path.states i) := by
    simpa [controller] using hedge
  simp only [sat_conj, sat_imp, sat_next]
  change (label (path.states i) .red = true → label (path.states (i + 1)) .green = true) ∧
    (label (path.states i) .green = true → label (path.states (i + 1)) .yellow = true) ∧
    (label (path.states i) .yellow = true → label (path.states (i + 1)) .red = true)
  rw [hnext]
  cases path.states i <;> decide

/-! ## Finite queries and checking with a supplied violation monitor -/

/-- List each phase once to fix route-search tie-breaking. `nodup` and
`complete` certify the enumeration; its order does not add model transitions. -/
def phaseOrder : Graph.Enumeration Phase where
  states := [.stop, .go, .caution]
  nodup := by decide
  complete phase := by cases phase <;> simp

-- Query reachable states, a route to yellow, and deadlocks. `route?` takes the
-- search order and a target phase; `none` would mean no initial route exists.
example : controller.reachableSet = Finset.univ := by
  simp only [FiniteKripke.reachableSet, Graph.reachableSet_eq_spec]
  decide
example : controller.route? phaseOrder .caution = some [.stop, .go, .caution] := by
  simp only [FiniteKripke.route?, Graph.route?_eq_spec]
  decide
example : controller.deadlocks = ∅ := by decide
example : stuckController.reachableDeadlocks = ∅ := by
  simp only [FiniteKripke.reachableDeadlocks, FiniteKripke.reachableSet, Graph.reachableSet_eq_spec]
  decide

/-!
`model.checkAgainst monitor serialProof` asks whether any initial execution
is accepted by the supplied monitor, returning true when no such violation
exists. `notEventually green` recognises words that never observe green;
`notResponse red green` recognises an unanswered red observation. The seriality
argument certifies continuation, not fairness. These small verdicts are proved
by rewriting to the finite search specification and using `decide`.
-/

/-- No execution of the normal controller can avoid green forever. -/
theorem controller_eventually_check :
    controller.checkAgainst (Monitors.notEventually Colour.green) controller_serial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- The added self-loop gives the violation monitor an accepting execution. -/
theorem stuck_eventually_check :
    stuckController.checkAgainst (Monitors.notEventually Colour.green) stuckController_serial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- No red observation goes unanswered in the normal cycle. -/
theorem controller_response_check :
    controller.checkAgainst (Monitors.notResponse Colour.red Colour.green) controller_serial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- Permanent red also violates the repeated response requirement. -/
theorem stuck_response_check :
    stuckController.checkAgainst (Monitors.notResponse Colour.red Colour.green) stuckController_serial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- Pass the seriality proof and the monitor's language theorem to
`checkAgainst_correct`; Lean infers the `_` arguments for monitor and formula.
Its forward direction turns the true verdict into universal LTL satisfaction. -/
theorem controller_eventually_green : controller.toKripke.Satisfies eventuallyGreen :=
  (controller.checkAgainst_correct _ controller_serial _
    (Monitors.notEventually_accepts Colour.green)).mp controller_eventually_check

/-- Use the response monitor's language theorem to obtain the matching LTL result. -/
theorem controller_red_responds : controller.toKripke.Satisfies redResponds :=
  (controller.checkAgainst_correct _ controller_serial _
    (Monitors.notResponse_accepts Colour.red Colour.green)).mp controller_response_check

/-! ## Understanding why the faulty controller fails -/

/-- A concrete counterexample, constructed explicitly rather than extracted
by the checker: stay in the red phase forever. -/
def stuckPath : stuckController.toKripke.Path where
  states := Cslib.ωSequence.const .stop
  valid _ := by
    change Phase.stop ∈ ({.stop, .go} : Finset Phase)
    decide

/-- The permanent-red trace starts initially, so it can refute a model property. -/
theorem stuckPath_initial : stuckPath.IsInitial := by
  change Phase.stop ∈ ({.stop} : Finset Phase)
  decide

/-- Every proposed eventual-green witness lies on a red-labelled state. -/
theorem stuckPath_never_green : ¬ WordSat stuckPath.word eventuallyGreen := by
  intro h
  obtain ⟨_, _, hgreen⟩ := sat_eventually.mp h
  change false = true at hgreen
  cases hgreen

/-- One initial violating path is enough to refute universal satisfaction. -/
theorem stuck_not_eventually_green : ¬ stuckController.toKripke.Satisfies eventuallyGreen :=
  fun h => stuckPath_never_green (h stuckPath stuckPath_initial)

/-- A second refutation obtained from the computed verdict and its language proof. -/
theorem stuck_not_red_responds : ¬ stuckController.toKripke.Satisfies redResponds := by
  intro h
  have htrue := (stuckController.checkAgainst_correct _ stuckController_serial _
    (Monitors.notResponse_accepts Colour.red Colour.green)).mpr h
  rw [stuck_response_check] at htrue
  cases htrue

-- Display (phase, red, green, yellow), a route, the two seriality tests, then
-- the normal/faulty verdict pairs. These executions do not create proof terms.
#eval (List.range 7).map fun i => (phaseAt i, cyclePath.word i .red,
  cyclePath.word i .green, cyclePath.word i .yellow)
#eval controller.route? phaseOrder .caution
#eval (controller.isSerial, stuckController.isSerial)
#eval (controller.checkAgainst (Monitors.notEventually Colour.green) controller_serial,
  stuckController.checkAgainst (Monitors.notEventually Colour.green) stuckController_serial)
#eval (controller.checkAgainst (Monitors.notResponse Colour.red Colour.green) controller_serial,
  stuckController.checkAgainst (Monitors.notResponse Colour.red Colour.green) stuckController_serial)

end Examples.TrafficLight
