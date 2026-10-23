import KILT.LTL.NormalForm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sets

/-!
# Finite subformulas of NNF

Collect syntax, not valuations. Duplicate occurrences collapse in the finite
set. This is bookkeeping for a later tableau, not an automaton construction.
Only this finite-set layer requires decidable equality on atom identifiers.
-/
namespace KILT.LTL.NNF
universe u
variable {AP : Type u}

/-- Count nodes in the internal syntax, before expansion to public formulas. -/
def size : NNF AP → Nat
  | .truth | .falsehood | .pos _ | .negAtom _ => 1
  | .next a => 1 + a.size
  | .conj a b | .disj a b | .until a b | .release a b => 1 + a.size + b.size

/-- Immediate syntactic children; order here has no semantic significance. -/
def children : NNF AP → List (NNF AP)
  | .truth | .falsehood | .pos _ | .negAtom _ => []
  | .next a => [a]
  | .conj a b | .disj a b | .until a b | .release a b => [a, b]

theorem child_size_lt {f g : NNF AP} (h : g ∈ f.children) : g.size < f.size := by
  cases f <;> simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals first | contradiction | (rcases h with rfl | rfl <;> simp only [size] <;> omega)

variable [DecidableEq AP]

/-- Root together with every descendant, without duplicates. -/
def subformulas : NNF AP → Finset (NNF AP)
  | f@(.truth) | f@(.falsehood) | f@(.pos _) | f@(.negAtom _) => {f}
  | f@(.next a) => insert f a.subformulas
  | f@(.conj a b) | f@(.disj a b) | f@(.until a b) | f@(.release a b) =>
      insert f (a.subformulas ∪ b.subformulas)

@[simp] theorem mem_subformulas_self (f : NNF AP) : f ∈ f.subformulas := by
  cases f <;> simp [subformulas]

/-- Recursive membership characterization covering every constructor. -/
theorem mem_subformulas_iff {f g : NNF AP} :
    g ∈ f.subformulas ↔ g = f ∨ ∃ child ∈ f.children, g ∈ child.subformulas := by
  cases f <;> simp [subformulas, children]

theorem child_subformulas_subset {f child : NNF AP} (h : child ∈ f.children) :
    child.subformulas ⊆ f.subformulas := by
  intro g hg
  exact mem_subformulas_iff.mpr (Or.inr ⟨child, h, hg⟩)

theorem child_mem_subformulas {f child : NNF AP} (h : child ∈ f.children) :
    child ∈ f.subformulas := child_subformulas_subset h (mem_subformulas_self child)

/-- Descending from any included formula never leaves the root's closure. -/
theorem subformulas_subset_of_mem {f g : NNF AP} (h : g ∈ f.subformulas) :
    g.subformulas ⊆ f.subformulas := by
  induction f using (measure size).wf.induction generalizing g with
  | h f ih =>
      rcases mem_subformulas_iff.mp h with rfl | ⟨child, hc, hg⟩
      · exact Finset.Subset.refl _
      · exact (ih child (child_size_lt hc) hg).trans (child_subformulas_subset hc)

theorem size_le_of_mem {f g : NNF AP} (h : g ∈ f.subformulas) : g.size ≤ f.size := by
  induction f using (measure size).wf.induction generalizing g with
  | h f ih =>
      rcases mem_subformulas_iff.mp h with rfl | ⟨child, hc, hg⟩
      · exact Nat.le_refl _
      · exact (ih child (child_size_lt hc) hg).trans (Nat.le_of_lt (child_size_lt hc))

private theorem card_insert_union_bound (f : NNF AP) (a b : Finset (NNF AP)) :
    (insert f (a ∪ b)).card ≤ a.card + b.card + 1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) 1)

/-- The number of distinct subformulas cannot exceed the number of nodes. -/
theorem card_subformulas_le_size (f : NNF AP) : f.subformulas.card ≤ f.size := by
  induction f with
  | truth | falsehood | pos _ | negAtom _ => simp [subformulas, size]
  | next a ha =>
      exact (Finset.card_insert_le _ _).trans (by simpa [size, Nat.add_comm] using Nat.add_le_add_right ha 1)
  | conj a b ha hb | disj a b ha hb | «until» a b ha hb | release a b ha hb =>
      apply (card_insert_union_bound _ a.subformulas b.subformulas).trans
      simp only [size]
      omega

/-- The finite carrier of subformulas for a later tableau state space. -/
abbrev Subformula (f : NNF AP) := {g // g ∈ f.subformulas}

instance (f : NNF AP) : Fintype (Subformula f) := FinsetCoe.fintype f.subformulas

end KILT.LTL.NNF
