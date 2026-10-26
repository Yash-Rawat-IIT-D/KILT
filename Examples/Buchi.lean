import KILT.Automata.Product
import KILT.Automata.Monitors
import Examples.FiniteKripke
import Examples.BuchiGraph

/-! # Computed Büchi checks and temporal regression cases -/
namespace Examples.Buchi
open KILT KILT.Automata Cslib Cslib.Automata
open scoped KILT.LTL

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev cycleSystem := Examples.FiniteKripke.RequestGrant.cycleFinite
abbrev waitingSystem := Examples.FiniteKripke.RequestGrant.waitingFinite

theorem cycleSerial : cycleSystem.toKripke.Serial := by
  rw [Examples.FiniteKripke.RequestGrant.cycle_toKripke]
  exact Examples.RequestGrant.cycle_serial

theorem waitingSerial : waitingSystem.toKripke.Serial := by
  rw [Examples.FiniteKripke.RequestGrant.waiting_toKripke]
  exact Examples.RequestGrant.waiting_serial

abbrev requestAtom := Examples.Syntax.Atom.request
abbrev grantAtom := Examples.Syntax.Atom.grant

theorem cycle_eventually_check :
    cycleSystem.checkAgainst (Monitors.notEventually grantAtom) cycleSerial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
theorem waiting_eventually_check :
    waitingSystem.checkAgainst (Monitors.notEventually grantAtom) waitingSerial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
theorem cycle_response_check :
    cycleSystem.checkAgainst (Monitors.notResponse requestAtom grantAtom) cycleSerial = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
theorem waiting_response_check :
    waitingSystem.checkAgainst (Monitors.notResponse requestAtom grantAtom) waitingSerial = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- The computed verdict entails the original universal temporal contract. -/
theorem cycle_response_from_checker :
    cycleSystem.toKripke.Satisfies Examples.RequestGrant.response := by
  exact (cycleSystem.checkAgainst_correct (Monitors.notResponse requestAtom grantAtom)
    cycleSerial _ (Monitors.notResponse_accepts requestAtom grantAtom)).mp cycle_response_check

theorem waiting_response_from_checker :
    ¬ waitingSystem.toKripke.Satisfies Examples.RequestGrant.response := by
  intro h
  have htrue := (waitingSystem.checkAgainst_correct (Monitors.notResponse requestAtom grantAtom)
    waitingSerial _ (Monitors.notResponse_accepts requestAtom grantAtom)).mpr h
  rw [waiting_response_check] at htrue
  cases htrue

theorem cycle_eventually_from_checker :
    cycleSystem.toKripke.Satisfies (LTL.Formula.eventually (.atom grantAtom)) :=
  (cycleSystem.checkAgainst_correct (Monitors.notEventually grantAtom) cycleSerial _
    (Monitors.notEventually_accepts grantAtom)).mp cycle_eventually_check

theorem waiting_eventually_from_checker :
    ¬ waitingSystem.toKripke.Satisfies (LTL.Formula.eventually (.atom grantAtom)) := by
  intro h
  have htrue := (waitingSystem.checkAgainst_correct (Monitors.notEventually grantAtom)
    waitingSerial _ (Monitors.notEventually_accepts grantAtom)).mpr h
  rw [waiting_eventually_check] at htrue
  cases htrue

/-- Four time positions, with the last position repeated forever. Atom 0 is
request, atom 1 is grant; other natural-number atoms are false. -/
def linear (requests grants : Finset (Fin 4)) : FiniteKripke (Fin 4) Nat where
  initials := {0}
  initials_nonempty := by simp
  successors state := {if state = 3 then 3 else state + 1}
  label state atom := if atom = 0 then decide (state ∈ requests)
    else if atom = 1 then decide (state ∈ grants) else false

theorem linearSerial (requests grants : Finset (Fin 4)) :
    (linear requests grants).toKripke.Serial := by
  intro state
  exact ⟨if state = 3 then 3 else state + 1, by simp [FiniteKripke.toKripke, linear]⟩

/-- Initial-position grant must be observed, even if grant never recurs. -/
example : (linear ∅ {0}).checkAgainst (Monitors.notEventually 1) (linearSerial ∅ {0}) = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear ∅ ∅).checkAgainst (Monitors.notResponse 0 1) (linearSerial ∅ ∅) = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear {0} {0}).checkAgainst (Monitors.notResponse 0 1) (linearSerial {0} {0}) = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear {0} {2}).checkAgainst (Monitors.notResponse 0 1) (linearSerial {0} {2}) = true := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear {0} ∅).checkAgainst (Monitors.notResponse 0 1) (linearSerial {0} ∅) = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear {0, 2} {1}).checkAgainst (Monitors.notResponse 0 1)
    (linearSerial {0, 2} {1}) = false := by
  simp only [FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

/-- The first edge uses the source's request/grant valuation. -/
example : (1, ()) ∉ (linear ∅ {0}).productSuccessors (Monitors.notEventually 1) (0, ()) := by decide
example : (1, ()) ∈ (linear ∅ {1}).productSuccessors (Monitors.notEventually 1) (0, ()) := by decide

def emptyInitials : FiniteBuchi Unit (LTL.Valuation Nat) where
  initials := ∅
  successors _ _ := {()}
  accepting := {()}

def emptyStates : FiniteBuchi (Fin 0) (LTL.Valuation Nat) where
  initials := ∅
  successors _ _ := ∅
  accepting := ∅

example : (linear ∅ ∅).hasAcceptedPath emptyInitials = false := by
  simp only [FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : (linear ∅ ∅).hasAcceptedPath emptyStates = false := by
  simp only [FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide
example : Examples.FiniteKripke.deadlockFinite.hasAcceptedPath
    (Monitors.notEventually grantAtom) = false := by
  simp only [FiniteKripke.hasAcceptedPath, Graph.hasAcceptingCycle_eq_spec]
  decide

#eval cycleSystem.checkAgainst (Monitors.notResponse requestAtom grantAtom) cycleSerial
#eval waitingSystem.checkAgainst (Monitors.notResponse requestAtom grantAtom) waitingSerial
#eval (linear ∅ {0}).checkAgainst (Monitors.notEventually 1) (linearSerial ∅ {0})
end Examples.Buchi
