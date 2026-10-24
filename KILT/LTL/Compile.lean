import KILT.LTL.TableauCorrect

/-!
# Verified formula compilation

Normalize, construct the explicit generalized tableau, then reuse the verified
round-robin conversion. The result has KILT's executable finite representation
and CSLib's Büchi language. Compilation needs equality on atoms, not a finite
atom type or an enumeration of valuations. Construction is exponential in the
number of normalized subformulas; this reference implementation is not an
optimized on-demand translator.
-/
namespace KILT.LTL.Formula
open Cslib.Automata
universe u
variable {AP : Type u} [DecidableEq AP]

/-- Tableau obligations paired with the next recurring-acceptance counter. -/
abbrev AutomatonState (φ : Formula AP) :=
  Tableau.State φ.normalize × (Tableau.toGeneralizedBuchi φ.normalize).Counter

/-- Executable finite automaton; its `.toBuchi` adapter uses CSLib acceptance. -/
def toBuchi (φ : Formula AP) : Automata.FiniteBuchi (AutomatonState φ) (Valuation AP) :=
  (Tableau.toGeneralizedBuchi φ.normalize).toFiniteBuchi

/-- Positive word-language theorem, independent of any Kripke model or seriality. -/
theorem toBuchi_accepts (φ : Formula AP) (word : Word AP) :
    ωAcceptor.Accepts φ.toBuchi.toBuchi word ↔ WordSat word φ := by
  rw [toBuchi, Tableau.toFiniteBuchi_accepts]
  exact φ.wordSat_normalize word

/-- At most the raw powerset size times the round-robin counter size. -/
theorem card_automatonState_le (φ : Formula AP) :
    Fintype.card (AutomatonState φ) ≤
      2 ^ φ.normalize.subformulas.card * max 1 (Tableau.untilObligations φ.normalize).length := by
  change Fintype.card (Tableau.State φ.normalize ×
    Fin (max 1 (Tableau.toGeneralizedBuchi φ.normalize).accepting.length)) ≤ _
  simp only [Fintype.card_prod, Fintype.card_fin, Tableau.toGeneralizedBuchi, List.length_map]
  exact Nat.mul_le_mul_right _ (Tableau.card_state_le _)

end KILT.LTL.Formula
