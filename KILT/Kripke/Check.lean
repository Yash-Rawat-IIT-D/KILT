import KILT.Kripke.PreparedCheck

/-!
# Formula-input model checking

Compile the negated formula and search the existing finite product for an
accepting cycle. CSLib supplies the run and acceptance semantics. Seriality is
an explicit public precondition; the underlying graph APIs still allow partial
models. No fairness is imposed, and false verdicts establish existence of an
infinite counterexample without extracting an executable witness.
-/
namespace KILT.FiniteKripke
open LTL Automata Cslib.Automata
universe u v w
variable {State : Type u} {AP : Type v} [Fintype State] [DecidableEq State] [DecidableEq AP]

/-- Check all initial infinite paths against the supplied LTL formula. -/
def check (M : FiniteKripke State AP) (φ : Formula AP) (hserial : M.toKripke.Serial) : Bool :=
  let compiled := (Formula.neg φ).compile
  Graph.Enumeration.runInvariant false
    (fun order => ((M.checker hserial order).prepareCompiled compiled).check)
    (fun _ _ => PreparedCheck.check_eq _ _)

/-- Compatibility with the existing supplied-monitor checking contract. -/
theorem check_eq_checkAgainst_violation (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) :
    M.check φ hserial = M.checkAgainst φ.violationAutomaton hserial := by
  unfold check
  apply Graph.Enumeration.runInvariant_eq
  intro order
  exact PreparedCheck.check_eq_checkAgainst _

/-- The computed verdict agrees with universal initial-path satisfaction. -/
theorem check_correct (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) :
    M.check φ hserial = true ↔ M.toKripke.Satisfies φ := by
  rw [check_eq_checkAgainst_violation]
  exact M.checkAgainst_correct φ.violationAutomaton hserial φ φ.violationAutomaton_accepts

/-- A false verdict means an actual infinite initial violating path exists. -/
theorem check_eq_false_iff (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) :
    M.check φ hserial = false ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ ¬ WordSat p.word φ := by
  rw [check_eq_checkAgainst_violation, checkAgainst, Bool.not_eq_false', hasAcceptedPath_eq_true_iff]
  exact exists_congr fun p => and_congr_right fun _ => φ.violationAutomaton_accepts p.word

/-- Any supplied monitor with the same violation language gives the same verdict. -/
theorem check_eq_checkAgainst (M : FiniteKripke State AP) (φ : Formula AP)
    (hserial : M.toKripke.Serial) {Q : Type w} [Fintype Q] [DecidableEq Q]
    (A : FiniteBuchi Q (Valuation AP))
    (hlanguage : ∀ word, ωAcceptor.Accepts A.toCSLib word ↔ ¬ WordSat word φ) :
    M.check φ hserial = M.checkAgainst A hserial := by
  apply Bool.eq_iff_iff.mpr
  exact (M.check_correct φ hserial).trans
    (M.checkAgainst_correct A hserial φ hlanguage).symm

theorem PreparedCheck.check_eq_check {M : FiniteKripke State AP} {φ : Formula AP}
    (problem : PreparedCheck M φ) :
    problem.check = M.check φ problem.execution.serial := by
  apply Bool.eq_iff_iff.mpr
  exact problem.check_correct.trans (M.check_correct φ problem.execution.serial).symm

end KILT.FiniteKripke
