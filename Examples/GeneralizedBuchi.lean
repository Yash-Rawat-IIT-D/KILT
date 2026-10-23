import KILT.Automata.GeneralizedBuchiCorrect
import Examples.TrafficLight

/-!
# Generalized acceptance worked examples

The graph tests fix a symbol, so a positive result means acceptance of the
constant word. Traffic examples instead let the existing product supply the
controller's valuations. These are existential path results, not universal LTL
verdicts. Every computed assertion below is kernel-checked with `decide`.
-/
namespace Examples.GeneralizedBuchi
open KILT KILT.Automata Cslib Cslib.Automata Filter

/-- Fixing a symbol exposes a finite graph suitable for the existing engine. -/
def verdict {Q Symbol : Type} [Fintype Q] [DecidableEq Q]
    (A : FiniteGeneralizedBuchi Q Symbol) (a : Symbol) : Bool :=
  Graph.hasAcceptingCycle A.toFiniteBuchi.initials
    (fun q => A.toFiniteBuchi.successors q a) A.toFiniteBuchi.accepting

theorem verdict_correct {Q Symbol : Type} [Fintype Q] [DecidableEq Q]
    (A : FiniteGeneralizedBuchi Q Symbol) (a : Symbol) :
    verdict A a = true ↔ A.Accepts ⟨fun _ => a⟩ := by
  rw [verdict, Graph.hasAcceptingCycle_eq_true_iff_run, ← A.toFiniteBuchi_accepts]
  constructor
  · rintro ⟨ss, hi, ht, ha⟩
    exact ⟨ss, ⟨hi, ht⟩, ha⟩
  · rintro ⟨ss, hr, ha⟩
    exact ⟨ss, hr.start, hr.trans, ha⟩

def loop (family : List (Finset Unit)) : FiniteGeneralizedBuchi Unit Nat where
  initials := {()}
  successors _ _ := {()}
  accepting := family

def deadlock : FiniteGeneralizedBuchi Unit Nat :=
  { loop [] with successors := fun _ _ => ∅ }
def noInitial : FiniteGeneralizedBuchi Unit Nat := { loop [] with initials := ∅ }
def emptyState : FiniteGeneralizedBuchi Empty Nat where
  initials := ∅
  successors q := nomatch q
  accepting := []

example : verdict (loop []) 37 = true := by decide
example : verdict deadlock 0 = false := by decide
example : verdict noInitial 0 = false := by decide
example : verdict emptyState 0 = false := by decide
example : verdict (loop [∅]) 0 = false := by decide
example : verdict (loop [{()}]) 0 = true := by decide
example : verdict (loop [{()}, {()}, {()}]) 0 = true := by decide
example : (loop []).Accepts ⟨fun _ => 37⟩ := (verdict_correct _ _).mp (by decide)
example : ¬ deadlock.Accepts ⟨fun _ => 0⟩ := by
  rw [← verdict_correct]; decide
example : ¬ (loop [∅]).Accepts ⟨fun _ => 0⟩ := by
  rw [← verdict_correct]; decide

/-- Two obligations with transitions selected by the symbol. -/
def alternating : FiniteGeneralizedBuchi Bool Nat where
  initials := {false}
  successors q a := {if a = 0 then !q else q}
  accepting := [{false}, {true}]

example : verdict alternating 0 = true := by decide
example : verdict alternating 1 = false := by decide
example : verdict { alternating with initials := {true} } 1 = false := by decide
/-- Visiting false once and then remaining true does not discharge false repeatedly. -/
example : verdict { alternating with successors := fun _ _ => {true} } 0 = false := by decide
example : verdict { alternating with accepting := [{true}, {false}, {true}] } 0 = true := by decide
example : verdict { alternating with accepting := [Finset.univ, {true}] } 0 = true := by decide

/-- A cyclic three-state graph exercises all counter values and wraparound. -/
def three : FiniteGeneralizedBuchi (Fin 3) Nat where
  initials := {0}
  successors q _ := {q + 1}
  accepting := [{0}, {1}, {2}]
example : verdict three 0 = true := by decide
example : (List.range 7).map (fun k => (three.liftSequence
    ⟨fun (j : Nat) => (⟨j % 3, Nat.mod_lt j (by decide)⟩ : Fin 3)⟩ k).2.val) = [0, 1, 2, 0, 1, 2, 0] := by decide
#eval (List.range 7).map (fun k => (three.liftSequence
  ⟨fun (j : Nat) => (⟨j % 3, Nat.mod_lt j (by decide)⟩ : Fin 3)⟩ k).2.val)

/-- The source false discharges obligation zero before the true successor is read. -/
example : (false, alternating.zero) ∈ alternating.toFiniteBuchi.initials := by decide
example : (true, (⟨1, by decide⟩ : alternating.Counter)) ∈
    alternating.toFiniteBuchi.successors (false, alternating.zero) 0 := by decide
/-- With the symbol selecting a self-loop, counter zero can become permanently stuck.
Accepting every counter-zero state would incorrectly accept this word. -/
example : verdict { alternating with initials := {true} } 1 = false := by decide
example : (true, alternating.zero) ∉ alternating.toFiniteBuchi.accepting := by decide

/-- Reordering and repeating obligations changes no word language. -/
theorem reordered (w : ωSequence Nat) :
    alternating.Accepts w ↔
      ({ alternating with accepting := [{true}, {false}, {true}] }).Accepts w := by
  refine FiniteGeneralizedBuchi.accepts_family_ext alternating
    { alternating with accepting := [{true}, {false}, {true}] } rfl rfl ?_ w
  intro F
  simp only [alternating, List.mem_cons, List.not_mem_nil, or_false]
  tauto

open TrafficLight
/-- State records the current colour observed on the preceding edge. Acceptance
requires green and yellow repeatedly; the one-edge lag preserves recurrence. -/
def recurringColours : FiniteGeneralizedBuchi (Fin 3) (LTL.Valuation Colour) where
  initials := {0}
  successors _ valuation :=
    {if valuation .green then 1 else if valuation .yellow then 2 else 0}
  accepting := [{1}, {2}]

/-- A genuinely red-only model; unlike stuckController it has no progressing branch. -/
def redOnly : FiniteKripke Unit Colour where
  initials := {()}
  initials_nonempty := by simp
  successors _ := {()}
  label _ := label .stop

theorem controller_recurs : controller.hasAcceptedPath recurringColours.toFiniteBuchi = true := by
  decide
theorem redOnly_does_not_recur : redOnly.hasAcceptedPath recurringColours.toFiniteBuchi = false := by
  decide
/-- Nondeterministic acceptance asks for some execution: the good cycle remains available. -/
example : stuckController.hasAcceptedPath recurringColours.toFiniteBuchi = true := by decide

theorem controller_has_recurring_path :
    ∃ p : controller.toKripke.Path, p.IsInitial ∧ recurringColours.Accepts p.word :=
  (controller.hasAcceptedPath_generalized_iff recurringColours).mp controller_recurs

#eval verdict three 0
#eval controller.hasAcceptedPath recurringColours.toFiniteBuchi
#eval redOnly.hasAcceptedPath recurringColours.toFiniteBuchi
end Examples.GeneralizedBuchi
