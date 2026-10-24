import KILT.Kripke.Check
import KILT.LTL.CompileOrder
import KILT.Graph.LassoSearch

/-!
# Executable counterexamples

The returned product lasso retains the automaton's acceptance evidence. Mapping
its states by Prod.fst gives a readable system lasso with exactly the same time
indices. Soundness concerns this actual trace, not an unrelated existence proof.
The existing Boolean checker and its global seriality boundary are unchanged.
-/
namespace KILT.FiniteKripke
open LTL Automata Cslib.Automata
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

def acceptedLasso? (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    Option (Graph.Lasso (State × Q)) :=
  Graph.acceptingLasso? (order.product automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (productAccepting A)

theorem acceptedLasso?_valid (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q)
    {l : Graph.Lasso (State × Q)} (h : M.acceptedLasso? A order automatonOrder = some l) :
    l.Valid (M.productInitials A) (M.productSuccessors A) ∧ l.entry ∈ productAccepting A :=
  Graph.acceptingLasso?_sound _ _ _ _ h

/-- Replay the actual product witness as a system path. -/
def productLassoPath (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) : M.toKripke.Path where
  states := l.sequence.map Prod.fst
  valid i := (Finset.mem_product.mp (h.step i)).1

@[simp] theorem productLassoPath_states (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) :
    (M.productLassoPath A l h).states = (l.map Prod.fst).sequence :=
  (l.map_sequence Prod.fst).symm

theorem productLassoPath_initial (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) :
    (M.productLassoPath A l h).IsInitial :=
  (Finset.mem_product.mp h.initial).1

theorem productLassoPath_accepts (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A))
    (ha : l.entry ∈ productAccepting A) :
    ωAcceptor.Accepts A.toBuchi (M.productLassoPath A l h).word := by
  have hr := (M.product_run_iff A (l.sequence.map Prod.fst) (l.sequence.map Prod.snd)).mp
    (show (l.sequence.map Prod.fst 0, l.sequence.map Prod.snd 0) ∈ M.productInitials A ∧
      ∀ i, (l.sequence.map Prod.fst (i + 1), l.sequence.map Prod.snd (i + 1)) ∈
        M.productSuccessors A (l.sequence.map Prod.fst i, l.sequence.map Prod.snd i) from
      by simpa only [Cslib.ωSequence.get_map, Prod.mk.eta, Graph.Step] using And.intro h.initial h.step)
  refine ⟨l.sequence.map Prod.snd, hr.2.2, ?_⟩
  have hacc : l.entry.2 ∈ A.accepting := (Finset.mem_product.mp ha).2
  exact l.frequently_entry.mono fun _ heq => by
    change (l.sequence _).2 ∈ A.accepting
    rw [heq]
    exact hacc

/-- A returned witness's own projection is initial and accepted. -/
theorem acceptedLasso?_sound (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q)
    {l : Graph.Lasso (State × Q)} (h : M.acceptedLasso? A order automatonOrder = some l) :
    let hv := (M.acceptedLasso?_valid A order automatonOrder h).1
    (M.productLassoPath A l hv).IsInitial ∧
      ωAcceptor.Accepts A.toBuchi (M.productLassoPath A l hv).word := by
  exact ⟨M.productLassoPath_initial A l _, M.productLassoPath_accepts A l _
    (M.acceptedLasso?_valid A order automatonOrder h).2⟩

theorem acceptedLasso?_isSome_iff (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    (M.acceptedLasso? A order automatonOrder).isSome = true ↔ M.hasAcceptedPath A = true :=
  Graph.acceptingLasso?_isSome_iff _ _ _ _

variable [DecidableEq AP]

/-- Extract a violating lasso; generate compiler order internally. No Boolean precheck. -/
def counterexample? (M : FiniteKripke State AP) (φ : Formula AP)
    (_hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    Option (Graph.Lasso (State × Formula.AutomatonState (.neg φ))) :=
  M.acceptedLasso? φ.violationAutomaton order (Formula.neg φ).automatonOrder

theorem counterexample?_valid (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State)
    {l : Graph.Lasso (State × Formula.AutomatonState (.neg φ))}
    (h : M.counterexample? φ hserial order = some l) :
    l.Valid (M.productInitials φ.violationAutomaton) (M.productSuccessors φ.violationAutomaton) :=
  (M.acceptedLasso?_valid φ.violationAutomaton order (Formula.neg φ).automatonOrder h).1

/-- The actual displayed trace violates the formula, including source position zero. -/
theorem counterexample?_sound (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State)
    {l : Graph.Lasso (State × Formula.AutomatonState (.neg φ))}
    (h : M.counterexample? φ hserial order = some l) :
    let p := M.productLassoPath φ.violationAutomaton l (M.counterexample?_valid φ hserial order h)
    p.IsInitial ∧ ¬ WordSat p.word φ := by
  have hs := M.acceptedLasso?_sound φ.violationAutomaton order (Formula.neg φ).automatonOrder h
  exact ⟨hs.1, (φ.violationAutomaton_accepts _).mp hs.2⟩

theorem counterexample?_isSome_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    (M.counterexample? φ hserial order).isSome = true ↔ M.check φ hserial = false := by
  rw [counterexample?, acceptedLasso?_isSome_iff, check, checkAgainst, Bool.not_eq_false']

theorem counterexample?_eq_none_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    M.counterexample? φ hserial order = none ↔ M.toKripke.Satisfies φ := by
  have h := M.counterexample?_isSome_iff φ hserial order
  rw [← M.check_correct φ hserial]
  cases hw : M.counterexample? φ hserial order <;> cases hc : M.check φ hserial <;>
    simp_all

end KILT.FiniteKripke
