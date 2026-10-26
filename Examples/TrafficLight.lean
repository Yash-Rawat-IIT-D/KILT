import KILT.Automata.Product
import KILT.Automata.Monitors

/-!
# A traffic light, from observations to verified verdicts

Read top to bottom: colour propositions -> state labels -> finite controller
-> an infinite path and its word -> safety proofs -> computed temporal checks.

One step is a logical tick, not a measured duration. This is a single light:
red -> green -> yellow -> red. The faulty version may stay red forever.
Both keep exactly one colour lit; only the first guarantees progress.

States and propositions are separate so later states can carry timers or
pedestrian requests while keeping the same colour observations. Multi-road
conflict rules, timed bounds and fairness remain extensions. Formula checking
and extracted lasso witnesses are demonstrated in the later checker modules.
-/

namespace Examples.TrafficLight

open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL

/-- Names observable by formulas; these are not the controller's states. -/
inductive Colour where
  | red | green | yellow
  deriving DecidableEq, Repr

/-- Internal controller states, deliberately separate from proposition names. -/
inductive Phase where
  | stop | go | caution
  deriving DecidableEq, Repr

instance : Fintype Phase where
  elems := {.stop, .go, .caution}
  complete phase := by cases phase <;> simp

/-- Each snapshot makes exactly one colour proposition true. -/
def label : Phase → Valuation Colour
  | .stop => fun colour => colour == .red
  | .go => fun colour => colour == .green
  | .caution => fun colour => colour == .yellow

def nextPhase : Phase → Phase
  | .stop => .go
  | .go => .caution
  | .caution => .stop

/-- The normal controller starts red and advances on every tick. -/
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

theorem controller_serial : controller.toKripke.Serial :=
  controller.isSerial_eq_true_iff.mp (by decide)

theorem stuckController_serial : stuckController.toKripke.Serial :=
  stuckController.isSerial_eq_true_iff.mp (by decide)

def red : Formula Colour := .atom .red
def green : Formula Colour := .atom .green
def yellow : Formula Colour := .atom .yellow

/-- Boolean syntax: at least one colour, and no pair simultaneously lit. -/
def oneColour : Formula Colour :=
  (red ∨ₗ green ∨ₗ yellow) ∧ₗ
  ¬ₗ (red ∧ₗ green) ∧ₗ ¬ₗ (red ∧ₗ yellow) ∧ₗ ¬ₗ (green ∧ₗ yellow)

def safety : Formula Colour := □ oneColour
def eventuallyGreen : Formula Colour := ◇ green
def redResponds : Formula Colour := □ (red ⟹ ◇ green)
def orderedColours : Formula Colour :=
  □ ((red ⟹ 𝒩 green) ∧ₗ (green ⟹ 𝒩 yellow) ∧ₗ (yellow ⟹ 𝒩 red))

/-- Explicit infinite execution: stop, go, caution, stop, ... -/
def phaseAt : Nat → Phase
  | 0 => .stop
  | n + 1 => nextPhase (phaseAt n)

def cyclePath : controller.toKripke.Path where
  states := ⟨phaseAt⟩
  valid i := by
    change phaseAt (i + 1) ∈ controller.successors (phaseAt i)
    simp [controller, phaseAt]

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

def phaseOrder : Graph.Enumeration Phase where
  states := [.stop, .go, .caution]
  nodup := by decide
  complete phase := by cases phase <;> simp

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

-- These decisions use the existing proved violation automata. They are not
-- yet produced automatically from `eventuallyGreen` or `redResponds`.
theorem controller_eventually_check :
    controller.checkAgainst (Monitors.notEventually Colour.green) controller_serial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

theorem stuck_eventually_check :
    stuckController.checkAgainst (Monitors.notEventually Colour.green) stuckController_serial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

theorem controller_response_check :
    controller.checkAgainst (Monitors.notResponse Colour.red Colour.green) controller_serial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

theorem stuck_response_check :
    stuckController.checkAgainst (Monitors.notResponse Colour.red Colour.green) stuckController_serial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- Computation entails satisfaction over ALL infinite initial paths. -/
theorem controller_eventually_green : controller.toKripke.Satisfies eventuallyGreen :=
  (controller.checkAgainst_correct _ controller_serial _
    (Monitors.notEventually_accepts Colour.green)).mp controller_eventually_check

theorem controller_red_responds : controller.toKripke.Satisfies redResponds :=
  (controller.checkAgainst_correct _ controller_serial _
    (Monitors.notResponse_accepts Colour.red Colour.green)).mp controller_response_check

/-- A concrete counterexample, constructed explicitly rather than extracted
by the checker: stay in the red phase forever. -/
def stuckPath : stuckController.toKripke.Path where
  states := Cslib.ωSequence.const .stop
  valid _ := by
    change Phase.stop ∈ ({.stop, .go} : Finset Phase)
    decide

theorem stuckPath_initial : stuckPath.IsInitial := by
  change Phase.stop ∈ ({.stop} : Finset Phase)
  decide

theorem stuckPath_never_green : ¬ WordSat stuckPath.word eventuallyGreen := by
  intro h
  obtain ⟨_, _, hgreen⟩ := sat_eventually.mp h
  change false = true at hgreen
  cases hgreen

theorem stuck_not_eventually_green : ¬ stuckController.toKripke.Satisfies eventuallyGreen :=
  fun h => stuckPath_never_green (h stuckPath stuckPath_initial)

/-- A second refutation obtained from the computed verdict and its language proof. -/
theorem stuck_not_red_responds : ¬ stuckController.toKripke.Satisfies redResponds := by
  intro h
  have htrue := (stuckController.checkAgainst_correct _ stuckController_serial _
    (Monitors.notResponse_accepts Colour.red Colour.green)).mpr h
  rw [stuck_response_check] at htrue
  cases htrue

-- Readable execution and graph diagnostics, followed by the four verdicts.
#eval (List.range 7).map fun i => (phaseAt i, cyclePath.word i .red,
  cyclePath.word i .green, cyclePath.word i .yellow)
#eval controller.route? phaseOrder .caution
#eval (controller.isSerial, stuckController.isSerial)
#eval (controller.checkAgainst (Monitors.notEventually Colour.green) controller_serial,
  stuckController.checkAgainst (Monitors.notEventually Colour.green) stuckController_serial)
#eval (controller.checkAgainst (Monitors.notResponse Colour.red Colour.green) controller_serial,
  stuckController.checkAgainst (Monitors.notResponse Colour.red Colour.green) stuckController_serial)

end Examples.TrafficLight
