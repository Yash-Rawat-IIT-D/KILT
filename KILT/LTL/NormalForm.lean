import KILT.LTL.Basic

/-!
# Negation normal form

Negation occurs only on atoms. Release is explicit because negating strong
until exchanges the two operators. `toFormula` interprets this internal syntax
in KILT's existing semantics; normalization introduces no second trace model.
All definitions and semantic proofs here work without atom equality or finiteness.
-/
namespace KILT.LTL
universe u

/-- Internal future-LTL syntax with literal negation only. -/
inductive NNF (AP : Type u) where
  | truth | falsehood
  | pos (atom : AP)
  | negAtom (atom : AP)
  | conj (left right : NNF AP)
  | disj (left right : NNF AP)
  | next (operand : NNF AP)
  | until (left right : NNF AP)
  | release (left right : NNF AP)
  deriving DecidableEq, Repr

namespace NNF
variable {AP : Type u}

/-- Interpret internal formulas using the public constructor basis. -/
def toFormula : NNF AP → Formula AP
  | .truth => .truth
  | .falsehood => .falsehood
  | .pos a => .atom a
  | .negAtom a => .neg (.atom a)
  | .conj a b => .conj a.toFormula b.toFormula
  | .disj a b => .disj a.toFormula b.toFormula
  | .next a => .next a.toFormula
  | .until a b => .until a.toFormula b.toFormula
  | .release a b => .release a.toFormula b.toFormula

/-- An abbreviation for the existing indexed semantics, not a new semantics. -/
abbrev Sat (w : Word AP) (i : Nat) (f : NNF AP) : Prop := LTL.Sat w i f.toFormula

@[simp] theorem sat_truth : Sat w i (.truth : NNF AP) ↔ True := LTL.sat_truth
@[simp] theorem sat_falsehood : Sat w i (.falsehood : NNF AP) ↔ False := Iff.rfl
@[simp] theorem sat_pos : Sat w i (.pos a : NNF AP) ↔ w i a = true := Iff.rfl
@[simp] theorem sat_negAtom : Sat w i (.negAtom a : NNF AP) ↔ ¬ w i a = true := Iff.rfl
@[simp] theorem sat_conj : Sat w i (.conj a b) ↔ Sat w i a ∧ Sat w i b := LTL.sat_conj
@[simp] theorem sat_disj : Sat w i (.disj a b) ↔ Sat w i a ∨ Sat w i b := Iff.rfl
@[simp] theorem sat_next : Sat w i (.next a) ↔ Sat w (i + 1) a := Iff.rfl
theorem sat_until : Sat w i (.until a b) ↔
    ∃ j, i ≤ j ∧ Sat w j b ∧ ∀ k, i ≤ k → k < j → Sat w k a := Iff.rfl
theorem sat_release : Sat w i (.release a b) ↔
    ∀ j, i ≤ j → (∀ k, i ≤ k → k < j → ¬ Sat w k a) → Sat w j b := LTL.sat_release

/-- Unfolding laws are explicit to avoid recursive simplification. -/
theorem sat_until_unfold : Sat w i (.until a b) ↔
    Sat w i b ∨ (Sat w i a ∧ Sat w (i + 1) (.until a b)) := LTL.sat_until_unfold

theorem sat_release_unfold : Sat w i (.release a b) ↔
    Sat w i b ∧ (Sat w i a ∨ Sat w (i + 1) (.release a b)) := LTL.sat_release_unfold

/-- Complement without introducing compound negation. -/
def negate : NNF AP → NNF AP
  | .truth => .falsehood
  | .falsehood => .truth
  | .pos a => .negAtom a
  | .negAtom a => .pos a
  | .conj a b => .disj a.negate b.negate
  | .disj a b => .conj a.negate b.negate
  | .next a => .next a.negate
  | .until a b => .release a.negate b.negate
  | .release a b => .until a.negate b.negate

@[simp] theorem negate_negate (f : NNF AP) : f.negate.negate = f := by
  induction f <;> simp_all [negate]

/-- Negation duality holds at every position, including the until endpoint. -/
@[simp] theorem sat_negate (f : NNF AP) (w : Word AP) (i : Nat) :
    Sat w i f.negate ↔ ¬ Sat w i f := by
  classical
  induction f generalizing i with
  | truth => simp [negate]
  | falsehood => simp [negate]
  | pos a => rfl
  | negAtom a => simp [negate]
  | conj a b ha hb =>
      simp only [negate, sat_disj, sat_conj, ha, hb]
      tauto
  | disj a b ha hb => simp [negate, ha, hb]
  | next a ha => simpa only [negate, sat_next] using ha (i + 1)
  | «until» a b ha hb =>
      simp only [negate, Sat, toFormula, Formula.release, LTL.sat_neg, LTL.sat_until]
      simp only [ha, hb, not_not]
  | release a b ha hb =>
      simp only [negate, Sat, toFormula, Formula.release, LTL.sat_neg, LTL.sat_until]
      simp only [ha, hb, not_not]

end NNF

namespace Formula
variable {AP : Type u}

/-- Structural normalization; this is not a Boolean or temporal minimizer. -/
def normalize : Formula AP → NNF AP
  | .falsehood => .falsehood
  | .atom a => .pos a
  | .neg a => a.normalize.negate
  | .disj a b => .disj a.normalize b.normalize
  | .next a => .next a.normalize
  | .until a b => .until a.normalize b.normalize

@[simp] theorem sat_normalize (f : Formula AP) (w : Word AP) (i : Nat) :
    NNF.Sat w i f.normalize ↔ LTL.Sat w i f := by
  induction f generalizing i with
  | falsehood => rfl
  | atom a => rfl
  | neg a ha => simpa only [normalize, NNF.sat_negate, LTL.sat_neg] using not_congr (ha i)
  | disj a b ha hb => simp only [normalize, NNF.sat_disj, LTL.sat_disj, ha, hb]
  | next a ha => simpa only [normalize, NNF.sat_next, LTL.sat_next] using ha (i + 1)
  | «until» a b ha hb => simp only [normalize, NNF.sat_until, LTL.sat_until, ha, hb]

theorem wordSat_normalize (f : Formula AP) (w : Word AP) :
    WordSat w f.normalize.toFormula ↔ WordSat w f := sat_normalize f w 0

theorem sat_normalize_neg (f : Formula AP) (w : Word AP) (i : Nat) :
    NNF.Sat w i (Formula.neg f).normalize ↔ ¬ LTL.Sat w i f := sat_normalize (.neg f) w i

@[simp] theorem normalize_truth : (truth : Formula AP).normalize = .truth := rfl
@[simp] theorem normalize_conj (a b : Formula AP) :
    (conj a b).normalize = .conj a.normalize b.normalize := by
  simp [conj, normalize, NNF.negate]
@[simp] theorem normalize_imp (a b : Formula AP) :
    (imp a b).normalize = .disj a.normalize.negate b.normalize := rfl
@[simp] theorem normalize_eventually (a : Formula AP) :
    (eventually a).normalize = .until .truth a.normalize := rfl
@[simp] theorem normalize_globally (a : Formula AP) :
    (globally a).normalize = .release .falsehood a.normalize := by
  simp [globally, eventually, normalize, truth, NNF.negate]
@[simp] theorem normalize_release (a b : Formula AP) :
    (release a b).normalize = .release a.normalize b.normalize := by
  simp [release, normalize, NNF.negate]

end Formula
end KILT.LTL
