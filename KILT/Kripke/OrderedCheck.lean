import KILT.Kripke.Check
import KILT.LTL.CompileOrder
import KILT.Graph.Buchi

/-! An explicit-order checker using only seed-reachable graph rows. -/
namespace KILT.FiniteKripke
open LTL Automata
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

def hasAcceptedPathWithOrder (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (modelOrder : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) : Bool :=
  Graph.hasAcceptingCycleWithOrder (modelOrder.product automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (productAccepting A)

theorem hasAcceptedPathWithOrder_eq (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (modelOrder : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    M.hasAcceptedPathWithOrder A modelOrder automatonOrder = M.hasAcceptedPath A :=
  Graph.hasAcceptingCycleWithOrder_eq _ _ _ _

variable [DecidableEq AP]

def checkWithOrder (M : FiniteKripke State AP) (φ : Formula AP)
    (_hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) : Bool :=
  !(M.hasAcceptedPathWithOrder φ.violationAutomaton modelOrder (Formula.neg φ).automatonOrder)

theorem checkWithOrder_eq_check (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkWithOrder φ hserial modelOrder = M.check φ hserial := by
  simp only [checkWithOrder, hasAcceptedPathWithOrder_eq, check, checkAgainst]

theorem checkWithOrder_correct (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkWithOrder φ hserial modelOrder = true ↔ M.toKripke.Satisfies φ := by
  rw [checkWithOrder_eq_check, check_correct]

theorem checkWithOrder_eq_false_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (modelOrder : Graph.Enumeration State) :
    M.checkWithOrder φ hserial modelOrder = false ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ ¬ WordSat p.word φ := by
  rw [checkWithOrder_eq_check, check_eq_false_iff]

theorem checkWithOrder_order_independent (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (first second : Graph.Enumeration State) :
    M.checkWithOrder φ hserial first = M.checkWithOrder φ hserial second := by
  rw [checkWithOrder_eq_check, checkWithOrder_eq_check]

end KILT.FiniteKripke
