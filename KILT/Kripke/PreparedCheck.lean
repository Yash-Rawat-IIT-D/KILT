import KILT.LTL.Compiled
import KILT.Automata.ProductLasso

set_option synthInstance.maxSize 1024

/-!
# Shared model-checking setup

Supply model order and seriality once. Compile a formula once, then prepare
one product for Boolean and optional-witness queries. Sharing is explicit
within an evaluation; pure definitions are not persistent caches.
-/
namespace KILT.FiniteKripke
open LTL Automata Cslib.Automata
universe u v
variable {State : Type u} {AP : Type v}
variable [Fintype State] [DecidableEq State] [DecidableEq AP]

/-- Execution policy for a serial finite model; unrelated models stay partial. -/
structure Checker (M : FiniteKripke State AP) where
  order : Graph.Enumeration State
  serial : M.toKripke.Serial

def checker (M : FiniteKripke State AP) (hserial : M.toKripke.Serial)
    (order : Graph.Enumeration State) : Checker M := ⟨order, hserial⟩

/-- The compiled violation language and its single prepared product. -/
structure PreparedCheck (M : FiniteKripke State AP) (φ : Formula AP) where
  execution : Checker M
  compiled : Formula.Compiled (.neg φ)
  product : M.PreparedProduct compiled.automaton execution.order compiled.order

/-- Reuse an already compiled violation formula, including across models. -/
def Checker.prepareCompiled {M : FiniteKripke State AP} (execution : Checker M)
    {φ : Formula AP} (compiled : Formula.Compiled (.neg φ)) : PreparedCheck M φ :=
  ⟨execution, compiled, M.prepareProduct compiled.automaton execution.order compiled.order⟩

def Checker.prepare {M : FiniteKripke State AP} (execution : Checker M)
    (φ : Formula AP) : PreparedCheck M φ :=
  execution.prepareCompiled (Formula.neg φ).compile

/-- Convenience constructor; both query methods consume this same prepared value. -/
def prepareCheck (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) (order : Graph.Enumeration State) : PreparedCheck M φ :=
  (M.checker hserial order).prepare φ

namespace PreparedCheck
variable {M : FiniteKripke State AP} {φ : Formula AP}

def check (problem : PreparedCheck M φ) : Bool := !problem.product.hasAcceptingCycle

def counterexample? (problem : PreparedCheck M φ) :
    Option (Graph.Lasso (State × Formula.AutomatonState (.neg φ))) :=
  problem.product.acceptingLasso?

/-- Readable system-state view; product timing and loop boundaries are preserved. -/
def systemCounterexample? (problem : PreparedCheck M φ) : Option (Graph.Lasso State) :=
  problem.counterexample?.map (Graph.Lasso.map Prod.fst)

theorem check_eq_checkAgainst (problem : PreparedCheck M φ) :
    problem.check = M.checkAgainst problem.compiled.automaton problem.execution.serial := by
  change (!problem.product.hasAcceptingCycle) = (!M.hasAcceptedPath problem.compiled.automaton)
  rw [Graph.PreparedSearch.hasAcceptingCycle_eq]
  rfl

theorem check_correct (problem : PreparedCheck M φ) :
    problem.check = true ↔ M.toKripke.Satisfies φ := by
  rw [problem.check_eq_checkAgainst]
  exact M.checkAgainst_correct problem.compiled.automaton problem.execution.serial φ
    problem.compiled.accepts_iff

theorem check_eq_false_iff (problem : PreparedCheck M φ) :
    problem.check = false ↔
      ∃ path : M.toKripke.Path, path.IsInitial ∧ ¬ WordSat path.word φ := by
  rw [problem.check_eq_checkAgainst, checkAgainst, Bool.not_eq_false', hasAcceptedPath_eq_true_iff]
  exact exists_congr fun path => and_congr_right fun _ => problem.compiled.accepts_iff path.word

theorem check_eq (a b : PreparedCheck M φ) : a.check = b.check := by
  apply Bool.eq_iff_iff.mpr
  exact a.check_correct.trans b.check_correct.symm

theorem counterexample?_valid (problem : PreparedCheck M φ)
    {l : Graph.Lasso (State × Formula.AutomatonState (.neg φ))}
    (h : problem.counterexample? = some l) :
    l.Valid (M.productInitials problem.compiled.automaton)
        (M.productSuccessors problem.compiled.automaton) ∧
      l.entry ∈ productAccepting problem.compiled.automaton :=
  problem.product.acceptingLasso?_sound h

def counterexamplePath (problem : PreparedCheck M φ)
    (l : Graph.Lasso (State × Formula.AutomatonState (.neg φ)))
    (h : problem.counterexample? = some l) : M.toKripke.Path :=
  M.productLassoPath problem.compiled.automaton l (problem.counterexample?_valid h).1

@[simp] theorem counterexamplePath_states (problem : PreparedCheck M φ)
    (l : Graph.Lasso (State × Formula.AutomatonState (.neg φ)))
    (h : problem.counterexample? = some l) :
    (problem.counterexamplePath l h).states = (l.map Prod.fst).sequence :=
  M.productLassoPath_states problem.compiled.automaton l _

/-- The returned witness's own projected infinite sequence violates the property. -/
theorem counterexample?_sound (problem : PreparedCheck M φ)
    {l : Graph.Lasso (State × Formula.AutomatonState (.neg φ))}
    (h : problem.counterexample? = some l) :
    (problem.counterexamplePath l h).IsInitial ∧
      ¬ WordSat (problem.counterexamplePath l h).word φ := by
  have valid := problem.counterexample?_valid h
  exact ⟨M.productLassoPath_initial _ _ valid.1,
    (problem.compiled.accepts_iff _).mp (M.productLassoPath_accepts _ _ valid.1 valid.2)⟩

theorem counterexample?_isSome_iff (problem : PreparedCheck M φ) :
    problem.counterexample?.isSome = true ↔ problem.check = false := by
  change problem.product.acceptingLasso?.isSome = true ↔ (!problem.product.hasAcceptingCycle) = false
  rw [problem.product.acceptingLasso?_isSome_iff, Bool.not_eq_false']

theorem counterexample?_eq_none_iff (problem : PreparedCheck M φ) :
    problem.counterexample? = none ↔ M.toKripke.Satisfies φ := by
  rw [← problem.check_correct]
  have h := problem.counterexample?_isSome_iff
  cases hw : problem.counterexample? <;> cases hc : problem.check <;> simp_all

end PreparedCheck
end KILT.FiniteKripke
