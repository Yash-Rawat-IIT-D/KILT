import KILT.LTL.Subformulas
import Cslib.Computability.Automata.NA.Basic

/-!
# Finite tableau states and local transitions

This module constructs the transition structure of the property automaton for
an NNF formula `f`. Its finite states are statically consistent assignments of
the subformulas of `f`: each state records the formulas claimed at one position
of an input valuation word. This is distinct from the Kripke automaton that
represents system executions.

An edge `s -v-> t` is valid when the claims in source state `s` agree with the
current valuation `v`, and its next, until, and release obligations evolve
consistently into target state `t`. Initial states claim `f` itself. These local
constraints still permit an until obligation to be postponed forever, so the
recurring acceptance conditions are added in `TableauAcceptance`.

No complementary formulas or valuations are enumerated.
-/
namespace KILT.LTL.Tableau
universe u
variable {AP : Type u} [DecidableEq AP]

/-- A candidate tableau snapshot: the finite set of subformulas of `f` marked
true at the current position. Formulas omitted from the set are unmarked;
logical and temporal consistency are imposed separately. -/
abbrev Assignment (f : NNF AP) := Finset (NNF.Subformula f)

/-- Test whether `g` is currently marked true in assignment `s`. Formulas
outside `f`'s subformula closure cannot occur in the assignment and therefore
do not hold. This is syntactic bookkeeping, not semantic `NNF.Sat`. -/
def Holds {f : NNF AP} (s : Assignment f) (g : NNF AP) : Prop :=
  if h : g ∈ f.subformulas then ⟨g, h⟩ ∈ s else False
instance {f : NNF AP} (s : Assignment f) (g : NNF AP) : Decidable (Holds s g) := by
  unfold Holds; infer_instance

@[simp] theorem holds_of_mem {f g : NNF AP} (s : Assignment f) (h : g ∈ f.subformulas) :
    Holds s g ↔ (⟨g, h⟩ : NNF.Subformula f) ∈ s := by simp [Holds, h]
@[simp] theorem not_holds_of_not_mem {f g : NNF AP} (s : Assignment f)
    (h : g ∉ f.subformulas) : ¬ Holds s g := by simp [Holds, h]

/-- The within-state consistency rule for constants and Boolean connectives.
Literal valuations and temporal relationships between states are checked by
the later local transition rules. -/
def StaticRule {f : NNF AP} (s : Assignment f) : NNF AP → Prop
  | .truth => Holds s .truth
  | .falsehood => ¬ Holds s .falsehood
  | .conj a b => Holds s (.conj a b) ↔ Holds s a ∧ Holds s b
  | .disj a b => Holds s (.disj a b) ↔ Holds s a ∨ Holds s b
  | _ => True
instance {f : NNF AP} (s : Assignment f) (g : NNF AP) : Decidable (StaticRule s g) := by
  cases g <;> unfold StaticRule <;> infer_instance

/-- An assignment is statically consistent when `StaticRule` holds for every
subformula of `f`; a proof supplies the certificate used by a tableau state. -/
def StaticConsistent {f : NNF AP} (s : Assignment f) : Prop :=
  ∀ g : NNF.Subformula f, StaticRule s g.val

instance {f : NNF AP} (s : Assignment f) : Decidable (StaticConsistent s) :=
  inferInstanceAs (Decidable (∀ g : NNF.Subformula f, StaticRule s g.val))

/-- Equivalent unbundled view of static consistency: every formula in the
computed subformula set obeys its within-state rule. -/
theorem staticConsistent_iff {f : NNF AP} (s : Assignment f) :
    StaticConsistent s ↔ ∀ g ∈ f.subformulas, StaticRule s g := by
  constructor
  · intro h g hg; exact h ⟨g, hg⟩
  · intro h g; exact h g.val g.property

/-- A tableau state is a statically consistent assignment for `f`. These states
form the finite nodes of the tableau; later transition rules relate them to
input valuations and to one another. -/
abbrev State (f : NNF AP) := {s : Assignment f // StaticConsistent s}

/-- The subtype Fintype filters the finite powerset, without classical selection. -/
instance (f : NNF AP) : Fintype (State f) := inferInstanceAs (Fintype {s : Assignment f // StaticConsistent s})

namespace State
variable {f : NNF AP}
/-- Test whether the assignment underlying a tableau state marks `g` true. -/
def holds (s : State f) (g : NNF AP) : Prop := Holds s.val g
instance (s : State f) (g : NNF AP) : Decidable (s.holds g) := inferInstanceAs (Decidable (Holds s.val g))

theorem rule (s : State f) {g : NNF AP} (hg : g ∈ f.subformulas) : StaticRule s.val g :=
  s.property ⟨g, hg⟩
theorem truth (s : State f) (h : NNF.truth ∈ f.subformulas) : s.holds .truth := s.rule h
theorem falsehood (s : State f) (h : NNF.falsehood ∈ f.subformulas) : ¬ s.holds .falsehood := s.rule h
theorem conj (s : State f) {a b} (h : NNF.conj a b ∈ f.subformulas) :
    s.holds (.conj a b) ↔ s.holds a ∧ s.holds b := s.rule h
theorem disj (s : State f) {a b} (h : NNF.disj a b ∈ f.subformulas) :
    s.holds (.disj a b) ↔ s.holds a ∨ s.holds b := s.rule h
end State

theorem card_state_le (f : NNF AP) : Fintype.card (State f) ≤ 2 ^ f.subformulas.card := by
  calc
    Fintype.card (State f) ≤ Fintype.card (Assignment f) := Fintype.card_subtype_le _
    _ = 2 ^ f.subformulas.card := by simp [Assignment, NNF.Subformula]

/-- The per-subformula condition for a candidate labelled tableau edge
`s -v-> t`. Literal claims in `s` must match the current valuation `v`, while
next, until, and release claims must evolve consistently from `s` to `t`.
Constants and Boolean connectives are already handled by static consistency. -/
def LocalRule {f : NNF AP} (s t : State f) (v : Valuation AP) : NNF AP → Prop
  | .pos p => s.holds (.pos p) ↔ v p = true
  | .negAtom p => s.holds (.negAtom p) ↔ v p = false
  | .next a => s.holds (.next a) ↔ t.holds a
  | .until a b => s.holds (.until a b) ↔ s.holds b ∨ (s.holds a ∧ t.holds (.until a b))
  | .release a b => s.holds (.release a b) ↔ s.holds b ∧ (s.holds a ∨ t.holds (.release a b))
  | _ => True
instance {f : NNF AP} (s t : State f) (v : Valuation AP) (g : NNF AP) :
    Decidable (LocalRule s t v g) := by cases g <;> unfold LocalRule <;> infer_instance

/-- A valid one-position transition of the tableau property automaton: every
relevant subformula obeys its local rule while the edge from `s` to `t`
consumes source-position valuation `v`. -/
def Step {f : NNF AP} (s t : State f) (v : Valuation AP) : Prop :=
  ∀ g : NNF.Subformula f, LocalRule s t v g.val
instance {f : NNF AP} (s t : State f) (v : Valuation AP) : Decidable (Step s t v) :=
  inferInstanceAs (Decidable (∀ g : NNF.Subformula f, LocalRule s t v g.val))

def LiteralRule {f : NNF AP} (s : State f) (v : Valuation AP) : NNF AP → Prop
  | .pos p => s.holds (.pos p) ↔ v p = true
  | .negAtom p => s.holds (.negAtom p) ↔ v p = false
  | _ => True
instance {f : NNF AP} (s : State f) (v : Valuation AP) (g : NNF AP) : Decidable (LiteralRule s v g) := by
  cases g <;> unfold LiteralRule <;> infer_instance

def TemporalRule {f : NNF AP} (s t : State f) : NNF AP → Prop
  | .next a => s.holds (.next a) ↔ t.holds a
  | .until a b => s.holds (.until a b) ↔ s.holds b ∨ (s.holds a ∧ t.holds (.until a b))
  | .release a b => s.holds (.release a b) ↔ s.holds b ∧ (s.holds a ∨ t.holds (.release a b))
  | _ => True
instance {f : NNF AP} (s t : State f) (g : NNF AP) : Decidable (TemporalRule s t g) := by
  cases g <;> unfold TemporalRule <;> infer_instance

def LiteralCompatible {f : NNF AP} (s : State f) (v : Valuation AP) : Prop :=
  ∀ g : NNF.Subformula f, LiteralRule s v g.val
instance {f : NNF AP} (s : State f) (v : Valuation AP) : Decidable (LiteralCompatible s v) :=
  inferInstanceAs (Decidable (∀ g : NNF.Subformula f, LiteralRule s v g.val))

def TemporalCompatible {f : NNF AP} (s t : State f) : Prop :=
  ∀ g : NNF.Subformula f, TemporalRule s t g.val
instance {f : NNF AP} (s t : State f) : Decidable (TemporalCompatible s t) :=
  inferInstanceAs (Decidable (∀ g : NNF.Subformula f, TemporalRule s t g.val))

theorem localRule_split {f : NNF AP} (s t : State f) (v : Valuation AP) (g : NNF AP) :
    LocalRule s t v g ↔ LiteralRule s v g ∧ TemporalRule s t g := by
  cases g <;> simp [LocalRule, LiteralRule, TemporalRule]

theorem step_split {f : NNF AP} (s t : State f) (v : Valuation AP) :
    Step s t v ↔ LiteralCompatible s v ∧ TemporalCompatible s t := by
  simp only [Step, LiteralCompatible, TemporalCompatible, ← forall_and]
  exact forall_congr' fun g => localRule_split s t v g.val


/-- Tableau states that claim the compiled root formula at position zero. -/
def initials (f : NNF AP) : Finset (State f) := Finset.univ.filter fun s => s.holds f
/-- Check source literals once before enumerating temporally compatible successors. -/
def successors {f : NNF AP} (s : State f) (v : Valuation AP) : Finset (State f) :=
  if LiteralCompatible s v then Finset.univ.filter fun t => TemporalCompatible s t else ∅

@[simp] theorem mem_initials {f : NNF AP} (s : State f) : s ∈ initials f ↔ s.holds f := by simp [initials]
@[simp] theorem mem_successors {f : NNF AP} (s t : State f) (v : Valuation AP) :
    t ∈ successors s v ↔ Step s t v := by
  by_cases h : LiteralCompatible s v
  · simp [successors, h, step_split]
  · simp [successors, h, step_split]

/-- The optimized set is extensionally the original local-rule filter. -/
theorem successors_eq_step_filter {f : NNF AP} (s : State f) (v : Valuation AP) :
    successors s v = Finset.univ.filter (fun t => Step s t v) := by
  ext t
  simp [mem_successors]

theorem successors_empty_of_incompatible {f : NNF AP} (s : State f) (v : Valuation AP)
    (h : ¬ LiteralCompatible s v) : successors s v = ∅ := by
  simp [successors, h]

/-- The tableau as a CSLib nondeterministic property automaton: its states are
consistent formula assignments and its valuation-labelled edges are `Step`. -/
def toNA (f : NNF AP) : Cslib.Automata.NA (State f) (Valuation AP) where
  start s := s ∈ initials f
  Tr s v t := t ∈ successors s v
@[simp] theorem toNA_start {f : NNF AP} (s : State f) : (toNA f).start s ↔ s.holds f := mem_initials s
@[simp] theorem toNA_transition {f : NNF AP} (s t : State f) (v : Valuation AP) :
    (toNA f).Tr s v t ↔ Step s t v := mem_successors s t v

theorem step_rule {f g : NNF AP} {s t : State f} {v : Valuation AP}
    (h : Step s t v) (hg : g ∈ f.subformulas) : LocalRule s t v g := h ⟨g, hg⟩

theorem step_pos {f : NNF AP} {s t : State f} {v : Valuation AP} {p : AP}
    (h : Step s t v) (hg : NNF.pos p ∈ f.subformulas) :
    s.holds (.pos p) ↔ v p = true := step_rule h hg

theorem step_negAtom {f : NNF AP} {s t : State f} {v : Valuation AP} {p : AP}
    (h : Step s t v) (hg : NNF.negAtom p ∈ f.subformulas) :
    s.holds (.negAtom p) ↔ v p = false := step_rule h hg

theorem step_next {f : NNF AP} {s t : State f} {v : Valuation AP} {a : NNF AP}
    (h : Step s t v) (hg : NNF.next a ∈ f.subformulas) :
    s.holds (.next a) ↔ t.holds a := step_rule h hg

theorem step_until {f : NNF AP} {s t : State f} {v : Valuation AP} {a b : NNF AP}
    (h : Step s t v) (hg : NNF.until a b ∈ f.subformulas) :
    s.holds (.until a b) ↔ s.holds b ∨ (s.holds a ∧ t.holds (.until a b)) := step_rule h hg

theorem step_release {f : NNF AP} {s t : State f} {v : Valuation AP} {a b : NNF AP}
    (h : Step s t v) (hg : NNF.release a b ∈ f.subformulas) :
    s.holds (.release a b) ↔ s.holds b ∧ (s.holds a ∨ t.holds (.release a b)) := step_rule h hg

/-- Exact semantic representation is an assumption, not a property of arbitrary states. -/
def Represents {f : NNF AP} (s : State f) (w : Word AP) (i : Nat) : Prop :=
  ∀ g ∈ f.subformulas, s.holds g ↔ NNF.Sat w i g

/-- Consecutive semantic assignments satisfy every local transition equation. -/
theorem step_of_represents {f : NNF AP} {s t : State f} {w : Word AP} {i : Nat}
    (hs : Represents s w i) (ht : Represents t w (i+1)) : Step s t (w i) := by
  intro ⟨g, hg⟩
  have child {a : NNF AP} (ha : a ∈ g.children) : a ∈ f.subformulas :=
    NNF.subformulas_subset_of_mem hg (NNF.child_mem_subformulas ha)
  cases g with
  | truth | falsehood | conj _ _ | disj _ _ => trivial
  | pos p => exact hs _ hg
  | negAtom p => simpa [LocalRule, NNF.sat_negAtom] using hs _ hg
  | next a =>
    change s.holds (.next a) ↔ t.holds a
    rw [hs _ hg, ht _ (child (by simp [NNF.children]))]
    rfl
  | «until» a b =>
    change s.holds (.until a b) ↔ s.holds b ∨ (s.holds a ∧ t.holds (.until a b))
    rw [hs _ hg, hs _ (child (by simp [NNF.children])),
      hs _ (child (by simp [NNF.children])), ht _ hg]
    exact sat_until_unfold
  | release a b =>
    change s.holds (.release a b) ↔ s.holds b ∧ (s.holds a ∨ t.holds (.release a b))
    rw [hs _ hg, hs _ (child (by simp [NNF.children])),
      hs _ (child (by simp [NNF.children])), ht _ hg]
    exact sat_release_unfold
end KILT.LTL.Tableau
