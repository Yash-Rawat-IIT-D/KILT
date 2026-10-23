import KILT.LTL.Subformulas
import Examples.TrafficLight
import Examples.Words

/-!
# Normalization and finite-subformula walkthrough

Normalize syntax without searching a word, then reuse the indexed semantic
theorem on arbitrary paths. The finite closure enumerates formula obligations,
not all valuations. It is preparation for a translator, not a formula checker.
-/
namespace Examples.Normalization
open KILT KILT.LTL
open scoped KILT.LTL

def p : Formula Nat := .atom 0
def q : Formula Nat := .atom 1

example : (¬ₗ (¬ₗ p)).normalize = .pos 0 := rfl
example : (¬ₗ (p ∨ₗ q)).normalize = .conj (.negAtom 0) (.negAtom 1) := rfl
example : (¬ₗ (p ∧ₗ q)).normalize = .disj (.negAtom 0) (.negAtom 1) := by decide
example : (p ⟹ q).normalize = .disj (.negAtom 0) (.pos 1) := rfl
example : (¬ₗ (𝒩 p)).normalize = .next (.negAtom 0) := rfl
example : (¬ₗ (p 𝒰 q)).normalize = .release (.negAtom 0) (.negAtom 1) := rfl
example : (¬ₗ (Formula.release p q)).normalize = .until (.negAtom 0) (.negAtom 1) := by decide
example : (◇ p).normalize = .until .truth (.pos 0) := rfl
example : (□ p).normalize = .release .falsehood (.pos 0) := by decide
example : (□ (p ⟹ ◇ q)).normalize =
    .release .falsehood (.disj (.negAtom 0) (.until .truth (.pos 1))) := by decide

/-- Atom equality is not an assumption of semantic normalization. -/
theorem arbitrary_atoms {AP : Type u} (f : Formula AP) (w : Word AP) (i : Nat) :
    NNF.Sat w i f.normalize ↔ Sat w i f := Formula.sat_normalize f w i

/-- Semantic preservation lifts to every initial path, even in partial models. -/
theorem model_normalization {State : Type u} {AP : Type v}
    (M : Kripke State AP) (f : Formula AP) :
    M.Satisfies f.normalize.toFormula ↔ M.Satisfies f := by
  constructor
  · intro h path hi
    exact (Formula.wordSat_normalize f path.word).mp (h path hi)
  · intro h path hi
    exact (Formula.wordSat_normalize f path.word).mpr (h path hi)

theorem traffic_safety :
    TrafficLight.controller.toKripke.Satisfies TrafficLight.safety.normalize.toFormula :=
  (model_normalization _ _).mpr TrafficLight.controller_safe

theorem traffic_ordering :
    TrafficLight.controller.toKripke.Satisfies TrafficLight.orderedColours.normalize.toFormula :=
  (model_normalization _ _).mpr TrafficLight.controller_ordered

theorem traffic_stuck_response :
    ¬ TrafficLight.stuckController.toKripke.Satisfies TrafficLight.redResponds.normalize.toFormula :=
  fun h => TrafficLight.stuck_not_red_responds ((model_normalization _ _).mp h)

-- Concrete infinite-word boundary cases use existing semantic proofs.
theorem until_now : NNF.Sat Examples.Words.never 0
    (Formula.until .falsehood (.neg Examples.Words.atom)).normalize :=
  (Formula.sat_normalize _ _ _).mpr Examples.Words.until_now

theorem no_postponed_until : ¬ NNF.Sat Examples.Words.always 0
    (Formula.until Examples.Words.atom .falsehood).normalize :=
  fun h => Examples.Words.until_requires_right ((Formula.sat_normalize _ _ _).mp h)

theorem release_forever : NNF.Sat Examples.Words.always 0
    (Formula.release .falsehood Examples.Words.atom).normalize :=
  (Formula.sat_normalize _ _ _).mpr Examples.Words.release_constant

theorem release_endpoint : ¬ NNF.Sat TrafficLight.cyclePath.word 0
    (Formula.release TrafficLight.green TrafficLight.red).normalize :=
  fun h => TrafficLight.not_green_release_red ((Formula.sat_normalize _ _ _).mp h)

example : NNF.Sat TrafficLight.cyclePath.word 0 (𝒩 TrafficLight.green).normalize :=
  (Formula.sat_normalize _ _ _).mpr (by rfl)
example : NNF.Sat TrafficLight.cyclePath.word 0 (◇ TrafficLight.red).normalize :=
  (Formula.sat_normalize _ _ _).mpr (sat_eventually_now rfl)

-- Exact finite syntax computations; Nat is an infinite atom identifier type.
example : (NNF.pos 0).subformulas = {NNF.pos (0 : Nat)} := rfl
example : (NNF.negAtom 0).subformulas = {NNF.negAtom (0 : Nat)} := rfl
example : (NNF.next (.pos 0)).subformulas =
    {.next (.pos (0 : Nat)), .pos 0} := by decide
example : (NNF.until (.pos 0) (.negAtom 1)).subformulas =
    {.until (.pos (0 : Nat)) (.negAtom 1), .pos 0, .negAtom 1} := by decide
example : (NNF.release (.pos 0) (.negAtom 1)).subformulas =
    {.release (.pos (0 : Nat)) (.negAtom 1), .pos 0, .negAtom 1} := by decide
example : (NNF.conj (.pos 0) (.pos 0)).subformulas.card = 2 := by decide
example : (NNF.disj (.pos 0) (.pos 0)).subformulas.card = 2 := by decide
example : (NNF.truth : NNF Nat).subformulas = {.truth} := rfl
example : (NNF.falsehood : NNF Nat).subformulas = {.falsehood} := rfl
example : Fintype.card (NNF.Subformula (NNF.conj (.pos (0 : Nat)) (.pos 0))) = 2 := by decide
example : DecidableEq (NNF.Subformula (NNF.pos (0 : Nat))) := inferInstance

/-- This response has seven distinct subformulas, including true and false. -/
def responseNNF := (□ (p ⟹ ◇ q)).normalize
example : responseNNF.subformulas.card = 7 := by decide

-- Inspect the internal tree and the finite set that will feed a later tableau.
#eval responseNNF
#eval responseNNF.subformulas
#eval (responseNNF.size, responseNNF.subformulas.card)

end Examples.Normalization
