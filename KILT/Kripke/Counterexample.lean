import KILT.Kripke.Check
import KILT.LTL.CompileOrder
import KILT.Automata.ProductLasso

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

variable [DecidableEq AP]

/-- Extract a violating lasso; generate compiler order internally. No Boolean precheck. -/
def counterexample? (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    Option (Graph.Lasso (State × Formula.AutomatonState (.neg φ))) :=
  (M.prepareCheck φ hserial order).counterexample?

theorem counterexample?_eq_acceptedLasso (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    M.counterexample? φ hserial order =
      M.acceptedLasso? φ.violationAutomaton order (Formula.neg φ).automatonOrder := rfl

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
  rw [counterexample?_eq_acceptedLasso, acceptedLasso?_isSome_iff,
    check_eq_checkAgainst_violation, checkAgainst, Bool.not_eq_false']

theorem counterexample?_eq_none_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) :
    M.counterexample? φ hserial order = none ↔ M.toKripke.Satisfies φ := by
  have h := M.counterexample?_isSome_iff φ hserial order
  rw [← M.check_correct φ hserial]
  cases hw : M.counterexample? φ hserial order <;> cases hc : M.check φ hserial <;>
    simp_all

end KILT.FiniteKripke
