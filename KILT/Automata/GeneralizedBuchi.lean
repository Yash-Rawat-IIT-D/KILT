import KILT.Automata.FiniteBuchi
import KILT.Automata.RoundRobin
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finite generalized Büchi automata

Each listed set must be visited arbitrarily late. The empty list still requires
an infinite initial run. Symbols are never enumerated. Conversion uses a source-
state round-robin counter, following the history-counter idea also used in
CSLib's `NA/BuchiInter.lean` (Ching-Tsun Chou, Apache 2.0), generalized here to
an executable arbitrary finite family.
-/
namespace KILT.Automata
open Filter
universe u v

structure FiniteGeneralizedBuchi (Q : Type u) (Symbol : Type v)
    [Fintype Q] [DecidableEq Q] where
  initials : Finset Q
  successors : Q → Symbol → Finset Q
  accepting : List (Finset Q)

namespace FiniteGeneralizedBuchi
variable {Q : Type u} {Symbol : Type v} [Fintype Q] [DecidableEq Q]

def toNA (A : FiniteGeneralizedBuchi Q Symbol) : Cslib.Automata.NA Q Symbol where
  start q := q ∈ A.initials
  Tr q a r := r ∈ A.successors q a

@[simp] theorem toNA_start (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) :
    A.toNA.start q ↔ q ∈ A.initials := Iff.rfl
@[simp] theorem toNA_transition (A : FiniteGeneralizedBuchi Q Symbol) (q r : Q) (a : Symbol) :
    A.toNA.Tr q a r ↔ r ∈ A.successors q a := Iff.rfl

/-- A generalized Büchi accepting run is a valid infinite run whose state
sequence visits every accepting set infinitely often. It need not visit every
state in those sets. For KILT's LTL tableau, each set records the recurring
discharge condition for one distinct until subformula. -/
def AcceptingRun (A : FiniteGeneralizedBuchi Q Symbol)
    (word : Cslib.ωSequence Symbol) (ss : Cslib.ωSequence Q) : Prop :=
  A.toNA.Run word ss ∧ ∀ F ∈ A.accepting, ∃ᶠ k in atTop, ss k ∈ F

/-- A word is accepted when some nondeterministically chosen state sequence is
both a valid run over that word and an accepting run for every generalized
Büchi obligation. -/
def Accepts (A : FiniteGeneralizedBuchi Q Symbol) (word : Cslib.ωSequence Symbol) : Prop :=
  ∃ ss, A.AcceptingRun word ss

/-- Two generalized Büchi automata with the same initial states and transitions
accept the same words when they contain the same accepting sets. Reordering or
duplicating those sets may change the later round-robin counter layout, but not
the generalized acceptance condition or language. -/
theorem accepts_family_ext (A B : FiniteGeneralizedBuchi Q Symbol)
    (hi : A.initials = B.initials) (ht : A.successors = B.successors)
    (hf : ∀ F, F ∈ A.accepting ↔ F ∈ B.accepting) (word : Cslib.ωSequence Symbol) :
    A.Accepts word ↔ B.Accepts word := by
  have hn : A.toNA = B.toNA := by cases A; cases B; simp_all [toNA]
  simp only [Accepts, AcceptingRun, hn]
  exact exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h F hF => h F ((hf F).mpr hF), fun h F hF => h F ((hf F).mp hF)⟩

abbrev Counter (A : FiniteGeneralizedBuchi Q Symbol) := Fin (max 1 A.accepting.length)

def zero (A : FiniteGeneralizedBuchi Q Symbol) : A.Counter := ⟨0, by omega⟩

/-- Missing obligations occur only for the empty family. -/
def hit (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter) : Bool :=
  decide (q ∈ A.accepting[i.val]?.getD ∅)

def advance (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter) : A.Counter :=
  if A.hit q i then
    if h : i.val + 1 < max 1 A.accepting.length then ⟨i.val + 1, h⟩ else A.zero
  else i

/-- Convert generalized acceptance to ordinary Büchi acceptance by using
product states `Q × A.Counter`. The first component follows the original run;
the counter component records which accepting set the round-robin construction
is currently waiting to hit. -/
def toFiniteBuchi (A : FiniteGeneralizedBuchi Q Symbol) : FiniteBuchi (Q × A.Counter) Symbol where
  initials := A.initials.image fun q => (q, A.zero)
  successors p a := (A.successors p.1 a).image fun r => (r, A.advance p.1 p.2)
  accepting := Finset.univ.filter fun p =>
    A.accepting.isEmpty ∨ (p.2 = A.zero ∧ A.hit p.1 p.2 = true)

/-- Converted initial states are original initial states paired with counter zero. -/
@[simp] theorem converted_start (A : FiniteGeneralizedBuchi Q Symbol) (p : Q × A.Counter) :
    p ∈ A.toFiniteBuchi.initials ↔ p.1 ∈ A.initials ∧ p.2 = A.zero := by
  simp [toFiniteBuchi, Prod.ext_iff]
  exact fun _ => eq_comm

/-- Converted transitions follow an original edge and deterministically advance its counter. -/
@[simp] theorem converted_transition (A : FiniteGeneralizedBuchi Q Symbol)
    (p r : Q × A.Counter) (a : Symbol) :
    r ∈ A.toFiniteBuchi.successors p a ↔
      r.1 ∈ A.successors p.1 a ∧ r.2 = A.advance p.1 p.2 := by
  simp [toFiniteBuchi, Prod.ext_iff]
  exact fun _ => eq_comm

/-- Converted acceptance is vacuous for no obligations and otherwise marks recurring round starts. -/
@[simp] theorem converted_accept (A : FiniteGeneralizedBuchi Q Symbol) (p : Q × A.Counter) :
    p ∈ A.toFiniteBuchi.accepting ↔
      A.accepting = [] ∨ (p.2 = A.zero ∧ A.hit p.1 p.2 = true) := by
  simp [toFiniteBuchi]

/-- Construct the unique round-robin counter sequence associated with an
original state sequence: start at zero and update from the state at each
position. This supplies the deterministic annotation used to lift runs. -/
def counter (A : FiniteGeneralizedBuchi Q Symbol) (ss : Cslib.ωSequence Q) : Nat → A.Counter
  | 0 => A.zero
  | k + 1 => A.advance (ss k) (A.counter ss k)

/-- Lift a state sequence into the product by pairing each state at position
`k` with its uniquely determined counter value at the same position. -/
def liftSequence (A : FiniteGeneralizedBuchi Q Symbol) (ss : Cslib.ωSequence Q) :
    Cslib.ωSequence (Q × A.Counter) := fun k => (ss k, A.counter ss k)

@[simp] theorem liftSequence_fst (A : FiniteGeneralizedBuchi Q Symbol)
    (ss : Cslib.ωSequence Q) (k : Nat) : (A.liftSequence ss k).1 = ss k := rfl

/-- Adding the deterministic counter annotation to an original run produces a
valid run of the converted product automaton. This can be visualised as zipping
the states and generating a valid product automaton run. -/
theorem lift_run (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence Q} (h : A.toNA.Run word ss) :
    A.toFiniteBuchi.toCSLib.Run word (A.liftSequence ss) := by
  constructor
  · exact (A.converted_start _).mpr ⟨h.start, rfl⟩
  · intro k
    exact (A.converted_transition _ _ _).mpr ⟨h.trans k, rfl⟩

/-- Projection by dropping the counter component from a converted product run recovers a
valid run of the original generalized automaton's underlying NA.  -/
theorem project_run (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (Q × A.Counter)} (h : A.toFiniteBuchi.toCSLib.Run word ss) :
    A.toNA.Run word (fun k => (ss k).1) := by
  constructor
  · exact ((A.converted_start _).mp h.start).1
  · intro k
    exact ((A.converted_transition _ _ _).mp (h.trans k)).1

/-- Every converted product run is exactly the canonical lift of its projected
original-state sequence. The counter starts at zero and each converted
transition determines its next value, so no alternative counter annotation can
form a valid run. -/
theorem run_eq_lift (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (Q × A.Counter)} (h : A.toFiniteBuchi.toCSLib.Run word ss) :
    ss = A.liftSequence (fun k => (ss k).1) := by
  have hc : ∀ k, (ss k).2 = A.counter (fun j => (ss j).1) k := by
    intro k
    induction k with
    | zero => exact ((A.converted_start _).mp h.start).2
    | succ k ih =>
      change (ss (k+1)).2 = A.advance (ss k).1 (A.counter (fun j => (ss j).1) k)
      rw [← ih]
      exact ((A.converted_transition _ _ _).mp (h.trans k)).2
  apply Cslib.ωSequence.ext
  intro k
  exact Prod.ext rfl (hc k)

/-- With one obligation, generalized acceptance is ordinary Büchi acceptance. -/
theorem accepts_singleton (A : FiniteGeneralizedBuchi Q Symbol) (F : Finset Q)
    (hf : A.accepting = [F]) (word : Cslib.ωSequence Symbol) :
    A.Accepts word ↔ Cslib.Automata.ωAcceptor.Accepts
      (FiniteBuchi.mk A.initials A.successors F).toCSLib word := by
  simp only [Accepts, AcceptingRun, hf, List.mem_singleton, forall_eq]
  rfl

end FiniteGeneralizedBuchi
end KILT.Automata
