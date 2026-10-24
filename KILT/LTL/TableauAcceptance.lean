import KILT.LTL.Tableau
import KILT.Automata.GeneralizedBuchi
import Mathlib.Data.List.Dedup

/-!
# Recurring tableau obligations

The local until equation permits indefinite postponement. Each distinct until
subformula therefore contributes an accepting set: it is absent, or fulfilled
now. Obligations follow syntax order, retaining the first occurrence. Release
is a greatest-fixpoint condition and contributes no recurring obligation.
This is an explicit tableau construction, rather than an on-demand algorithm;
see Gerth, Peled, Vardi and Wolper, https://www.cs.rice.edu/~vardi/papers/pstv95rj.pdf.
-/
namespace KILT.LTL.Tableau
universe u
variable {AP : Type u} [DecidableEq AP]

/-- Root-first, left-to-right traversal, including repeated occurrences. -/
def preorder : NNF AP → List (NNF AP)
  | f@(.truth) | f@(.falsehood) | f@(.pos _) | f@(.negAtom _) => [f]
  | f@(.next a) => f :: preorder a
  | f@(.conj a b) | f@(.disj a b) | f@(.until a b) | f@(.release a b) =>
      f :: (preorder a ++ preorder b)

@[simp] theorem mem_preorder {f g : NNF AP} : g ∈ preorder f ↔ g ∈ f.subformulas := by
  induction f <;> simp_all [preorder, NNF.subformulas]

def isUntil : NNF AP → Bool
  | .until _ _ => true
  | _ => false

omit [DecidableEq AP] in
theorem isUntil_iff {g : NNF AP} : isUntil g = true ↔ ∃ a b, g = .until a b := by
  cases g <;> simp [isUntil]

/-- Reversing before and after last-occurrence dedup retains first occurrences. -/
def untilObligations (f : NNF AP) : List (NNF AP) :=
  (((preorder f).filter isUntil).reverse.dedup).reverse

theorem untilObligations_nodup (f : NNF AP) : (untilObligations f).Nodup :=
  List.nodup_reverse.mpr (List.nodup_dedup _)

@[simp] theorem mem_untilObligations {f g : NNF AP} :
    g ∈ untilObligations f ↔ g ∈ f.subformulas ∧ isUntil g = true := by
  simp [untilObligations]

@[simp] theorem until_mem_untilObligations {f a b : NNF AP} :
    NNF.until a b ∈ untilObligations f ↔ NNF.until a b ∈ f.subformulas := by
  simp [isUntil]

theorem length_untilObligations_le (f : NNF AP) :
    (untilObligations f).length ≤ f.subformulas.card := by
  rw [← List.toFinset_card_of_nodup (untilObligations_nodup f)]
  apply Finset.card_le_card
  intro g hg
  exact (mem_untilObligations.mp (List.mem_toFinset.mp hg)).1

/-- The non-until branch is unused in the acceptance family. -/
def acceptanceSet (f : NNF AP) : NNF AP → Finset (State f)
  | g@(.until _ b) => Finset.univ.filter fun s => ¬ s.holds g ∨ s.holds b
  | _ => Finset.univ

@[simp] theorem mem_acceptanceSet {f a b : NNF AP} (s : State f) :
    s ∈ acceptanceSet f (.until a b) ↔ ¬ s.holds (.until a b) ∨ s.holds b := by
  simp [acceptanceSet]

def toGeneralizedBuchi (f : NNF AP) :
    Automata.FiniteGeneralizedBuchi (State f) (Valuation AP) where
  initials := initials f
  successors := successors
  accepting := (untilObligations f).map (acceptanceSet f)

@[simp] theorem toGeneralizedBuchi_toNA (f : NNF AP) :
    (toGeneralizedBuchi f).toNA = toNA f := rfl

/-- Every until has an obligation, even if two resulting sets coincide. -/
theorem acceptanceSet_mem {f a b : NNF AP} (h : NNF.until a b ∈ f.subformulas) :
    acceptanceSet f (.until a b) ∈ (toGeneralizedBuchi f).accepting :=
  List.mem_map.mpr ⟨_, until_mem_untilObligations.mpr h, rfl⟩

end KILT.LTL.Tableau
