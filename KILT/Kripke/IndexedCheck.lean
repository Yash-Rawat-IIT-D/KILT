import KILT.Kripke.Check
import KILT.LTL.CompileOrder
import KILT.Graph.IndexedBuchi

/-! An explicit-order checker using only seed-reachable graph rows. -/
namespace KILT.FiniteKripke
open LTL Automata
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

def hasAcceptedPathIndexed (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (modelOrder : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) : Bool :=
  Graph.hasAcceptingCycleIndexed (modelOrder.product automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (productAccepting A)

theorem hasAcceptedPathIndexed_eq (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (modelOrder : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    M.hasAcceptedPathIndexed A modelOrder automatonOrder = M.hasAcceptedPath A :=
  Graph.hasAcceptingCycleIndexed_eq _ _ _ _

variable [DecidableEq AP]

def checkIndexed (M : FiniteKripke State AP) (φ : Formula AP)
    (_hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) : Bool :=
  !(M.hasAcceptedPathIndexed φ.violationAutomaton modelOrder (Formula.neg φ).automatonOrder)

theorem checkIndexed_eq_check (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkIndexed φ hserial modelOrder = M.check φ hserial := by
  simp only [checkIndexed, hasAcceptedPathIndexed_eq, check, checkAgainst]

theorem checkIndexed_correct (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkIndexed φ hserial modelOrder = true ↔ M.toKripke.Satisfies φ := by
  rw [checkIndexed_eq_check, check_correct]

theorem checkIndexed_eq_false_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkIndexed φ hserial modelOrder = false ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ ¬ WordSat p.word φ := by
  rw [checkIndexed_eq_check, check_eq_false_iff]

theorem checkIndexed_order_independent (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (first second : Graph.Enumeration State) :
    M.checkIndexed φ hserial first = M.checkIndexed φ hserial second := by
  rw [checkIndexed_eq_check, checkIndexed_eq_check]

end KILT.FiniteKripke
