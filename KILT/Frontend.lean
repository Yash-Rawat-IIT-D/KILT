import KILT.Kripke.Check
import KILT.Kripke.Counterexample

/-!
# Lightweight user frontend

This module keeps convenience syntax and presentation data above the verified
checker API. The tactics expand to ordinary kernel-checked proofs; result
rendering does not create a theorem or replace counterexample soundness.
-/

namespace KILT

/-- Prove a small closed `FiniteKripke.check` verdict using the verified
implementation-to-specification rewrites followed by kernel `decide`.

This is intended for examples and manageable concrete models. It is not an
alias for compiled evaluation, and large instances may exceed kernel reduction
limits even when `#eval` completes. -/
macro "kilt_decide" : tactic =>
  `(tactic|
    simp only [FiniteKripke.check_eq_checkAgainst_violation,
      FiniteKripke.checkAgainst, FiniteKripke.hasAcceptedPath,
      Graph.hasAcceptingCycle_eq_spec]
    <;> decide)

/-- Prove global seriality of a small closed finite model by checking that its
deadlock set is empty and applying `isSerial_eq_true_iff`.

This proves that every state has a successor. It does not add transitions or
establish fairness. -/
macro "kilt_serial" : tactic =>
  `(tactic|
    exact (FiniteKripke.isSerial_eq_true_iff _).mp (by decide))

namespace FiniteKripke

/-- Presentation-oriented result using only system states. Constructing this
result performs witness extraction and derives the verdict from witness
absence; use `PreparedCheck.check` when only the Boolean is required. -/
structure SystemCheckResult (State : Type u) where
  verdict : Bool
  counterexample? : Option (Graph.Lasso State)

namespace SystemCheckResult

private def renderStates {State : Type u} (renderState : State → String)
    (states : List State) : String :=
  "[" ++ String.intercalate ", " (states.map renderState) ++ "]"

/-- Render the stable lasso concepts without making `Repr` output part of any
semantic or proof contract. -/
def render {State : Type u} (result : SystemCheckResult State)
    (renderState : State → String) (replayCount : Nat := 8) : String :=
  let header :=
    s!"check={result.verdict}, counterexample present={result.counterexample?.isSome}"
  match result.counterexample? with
  | none => header ++ "\n  no initial violating execution"
  | some lasso =>
      String.intercalate "\n" [
        header,
        s!"  prefix, played once: {renderStates renderState lasso.prefix}",
        s!"  loop, repeated forever: {renderStates renderState lasso.loop}",
        s!"  first {replayCount} states: {renderStates renderState (lasso.replay replayCount)}"
      ]

/-- `Repr`-based convenience renderer for examples and interactive use. -/
def renderRepr {State : Type u} [Repr State] (result : SystemCheckResult State)
    (replayCount : Nat := 8) : String :=
  result.render reprStr replayCount

end SystemCheckResult

namespace PreparedCheck

variable {State : Type u} {AP : Type v}
variable [Fintype State] [DecidableEq State] [DecidableEq AP]
variable {M : FiniteKripke State AP} {φ : LTL.Formula AP}

/-- Extract at most one system-state lasso and derive the matching verdict from
that same result. This avoids separately running both the Boolean search and
witness extraction when a caller needs both for presentation. -/
def runSystem (problem : PreparedCheck M φ) : SystemCheckResult State :=
  let counterexample := problem.systemCounterexample?
  ⟨counterexample.isNone, counterexample⟩

@[simp] theorem runSystem_counterexample? (problem : PreparedCheck M φ) :
    problem.runSystem.counterexample? = problem.systemCounterexample? := rfl

/-- The presentation result reports exactly the verified prepared verdict. -/
@[simp] theorem runSystem_verdict (problem : PreparedCheck M φ) :
    problem.runSystem.verdict = problem.check := by
  unfold runSystem
  have h := problem.counterexample?_isSome_iff
  cases hw : problem.counterexample? <;> cases hc : problem.check <;>
    simp_all [systemCounterexample?]

end PreparedCheck
end FiniteKripke
end KILT
