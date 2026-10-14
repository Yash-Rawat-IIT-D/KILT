import KILT.Kripke.Path
import KILT.LTL.Basic

/-!
# LTL satisfaction over Kripke structures

This module will define when a Kripke structure satisfies an LTL formula: all
of its initial paths must satisfy the formula's word semantics at position zero.
-/

namespace KILT.Kripke

universe u v

variable {State : Type u} {AP : Type v}

/-- A model satisfies an LTL formula when every infinite initial path does.
For a partial model with no infinite initial path this proposition is
vacuously true. -/
def Satisfies (M : KILT.Kripke State AP) (formula : LTL.Formula AP) : Prop :=
  ∀ p : M.Path, p.IsInitial → LTL.WordSat p.word formula

end KILT.Kripke
