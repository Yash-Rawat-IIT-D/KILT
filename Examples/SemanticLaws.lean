import KILT.LTL.Basic
import Examples.Syntax
import Examples.Words

/-!
# Semantic-law regression examples

These examples use the general laws from `KILT.LTL.Basic` on concrete words.
They cover suffix offsets, until unfolding, release's inclusive boundary, and
the request/grant property `G(request → F grant)`. They complement Section 1's
syntax/equality checks and direct constructor examples.
-/

namespace Examples.SemanticLaws

open KILT.LTL
open Examples.Words

-- Next is evaluated after the prefix has been dropped.
example : Sat (alternating.drop 1) 0 (.next atom) := by
  rw [sat_drop]
  rfl

-- Both the dropped prefix and the evaluation position may be nonzero.
example : Sat (alternating.drop 2) 3 (.next atom) := by
  rw [sat_drop]
  rfl

example : ¬ WordSat (alternating.drop 1) atom := by
  rw [wordSat_drop]
  intro h
  cases h

-- Shifting a temporal formula, rather than just an atom, uses the same law.
example : WordSat (alternating.drop 1) (Formula.eventually atom) := by
  rw [wordSat_drop]
  exact eventually_later

example : WordSat never (.until .falsehood (.neg atom)) := by
  apply sat_until_now
  intro h
  cases h

-- The later-witness example has a genuine until obligation at the next step.
theorem until_after_first_step :
    Sat requestThenGrant 1 (.until (.atom false) (.atom true)) := by
  rcases sat_until_unfold.mp until_later with hnow | ⟨_, hnext⟩
  · cases hnow
  · exact hnext

-- Conjunction and implication are interpreted through their general laws.
example : WordSat always (Formula.conj atom (.next atom)) := by
  exact sat_conj.mpr ⟨rfl, rfl⟩

example : WordSat never (Formula.imp atom .falsehood) := by
  apply sat_imp.mpr
  intro h
  cases h

-- A true left operand does not excuse a false right operand at position zero.
theorem release_requires_right_now :
    ¬ WordSat never (Formula.release (.neg atom) atom) := by
  intro h
  have hright := sat_release.mp h 0 (Nat.le_refl 0) (by
    intro k hlow hhigh
    omega)
  cases hright

-- Both operands hold at zero; later right values may then be false.
theorem release_can_finish_now :
    WordSat requestThenGrant (Formula.release (.atom false) (.atom false)) := by
  apply sat_release.mpr
  intro j _ hprefix
  by_cases hj : j = 0
  · subst j
    rfl
  · have hnot := hprefix 0 (Nat.le_refl 0) (by omega)
    exact (hnot rfl).elim

theorem request_not_globally_true :
    ¬ WordSat requestThenGrant (Formula.globally (.atom false)) := by
  intro h
  have hrequest := sat_globally.mp h 1 (by decide)
  cases hrequest

/-- Every request has a grant now or later. These are named syntax atoms. -/
def response : Formula Syntax.Atom :=
  Formula.globally (Formula.imp Syntax.request (Formula.eventually Syntax.grant))

-- A valuation word over the same names used in the syntax examples.
def granting : Word Syntax.Atom := ⟨fun i a => match a with
  | .request => decide (i = 0)
  | .grant => decide (1 ≤ i)⟩

def stalled : Word Syntax.Atom := Cslib.ωSequence.const (fun a => match a with
  | .request => true
  | .grant => false)

theorem response_holds : WordSat granting response := by
  apply sat_globally.mpr
  intro i _
  apply sat_imp.mpr
  intro _
  apply sat_eventually.mpr
  refine ⟨i + 1, by omega, ?_⟩
  change decide (1 ≤ i + 1) = true
  have h : 1 ≤ i + 1 := by omega
  simp [h]

theorem response_fails : ¬ WordSat stalled response := by
  intro h
  have hAtZero := sat_globally.mp h 0 (Nat.le_refl 0)
  have hEventually := sat_imp.mp hAtZero (show Sat stalled 0 Syntax.request from rfl)
  rcases sat_eventually.mp hEventually with ⟨_, _, hGrant⟩
  cases hGrant

end Examples.SemanticLaws

-- Include the main proof dependencies in the build log for review.
-- Standard Lean axioms are expected; `sorryAx` would indicate an unfinished proof.
#print axioms KILT.LTL.sat_until_unfold
#print axioms KILT.LTL.sat_drop
#print axioms KILT.LTL.sat_release
#print axioms Examples.SemanticLaws.response_holds
#print axioms Examples.SemanticLaws.response_fails
