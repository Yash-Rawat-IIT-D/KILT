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

def AcceptingRun (A : FiniteGeneralizedBuchi Q Symbol)
    (word : Cslib.ωSequence Symbol) (ss : Cslib.ωSequence Q) : Prop :=
  A.toNA.Run word ss ∧ ∀ F ∈ A.accepting, ∃ᶠ k in atTop, ss k ∈ F

def Accepts (A : FiniteGeneralizedBuchi Q Symbol) (word : Cslib.ωSequence Symbol) : Prop :=
  ∃ ss, A.AcceptingRun word ss

/-- Ordered obligations affect counter layout, but their membership determines language. -/
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

def toFiniteBuchi (A : FiniteGeneralizedBuchi Q Symbol) : FiniteBuchi (Q × A.Counter) Symbol where
  initials := A.initials.image fun q => (q, A.zero)
  successors p a := (A.successors p.1 a).image fun r => (r, A.advance p.1 p.2)
  accepting := Finset.univ.filter fun p =>
    A.accepting.isEmpty ∨ (p.2 = A.zero ∧ A.hit p.1 p.2 = true)

@[simp] theorem converted_start (A : FiniteGeneralizedBuchi Q Symbol) (p : Q × A.Counter) :
    p ∈ A.toFiniteBuchi.initials ↔ p.1 ∈ A.initials ∧ p.2 = A.zero := by
  simp [toFiniteBuchi, Prod.ext_iff]
  exact fun _ => eq_comm

@[simp] theorem converted_transition (A : FiniteGeneralizedBuchi Q Symbol)
    (p r : Q × A.Counter) (a : Symbol) :
    r ∈ A.toFiniteBuchi.successors p a ↔
      r.1 ∈ A.successors p.1 a ∧ r.2 = A.advance p.1 p.2 := by
  simp [toFiniteBuchi, Prod.ext_iff]
  exact fun _ => eq_comm

@[simp] theorem converted_accept (A : FiniteGeneralizedBuchi Q Symbol) (p : Q × A.Counter) :
    p ∈ A.toFiniteBuchi.accepting ↔
      A.accepting = [] ∨ (p.2 = A.zero ∧ A.hit p.1 p.2 = true) := by
  simp [toFiniteBuchi]

def counter (A : FiniteGeneralizedBuchi Q Symbol) (ss : Cslib.ωSequence Q) : Nat → A.Counter
  | 0 => A.zero
  | k + 1 => A.advance (ss k) (A.counter ss k)

def liftSequence (A : FiniteGeneralizedBuchi Q Symbol) (ss : Cslib.ωSequence Q) :
    Cslib.ωSequence (Q × A.Counter) := fun k => (ss k, A.counter ss k)

@[simp] theorem liftSequence_fst (A : FiniteGeneralizedBuchi Q Symbol)
    (ss : Cslib.ωSequence Q) (k : Nat) : (A.liftSequence ss k).1 = ss k := rfl

theorem lift_run (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence Q} (h : A.toNA.Run word ss) :
    A.toFiniteBuchi.toBuchi.Run word (A.liftSequence ss) := by
  constructor
  · exact (A.converted_start _).mpr ⟨h.start, rfl⟩
  · intro k
    exact (A.converted_transition _ _ _).mpr ⟨h.trans k, rfl⟩

theorem project_run (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (Q × A.Counter)} (h : A.toFiniteBuchi.toBuchi.Run word ss) :
    A.toNA.Run word (fun k => (ss k).1) := by
  constructor
  · exact ((A.converted_start _).mp h.start).1
  · intro k
    exact ((A.converted_transition _ _ _).mp (h.trans k)).1

/-- Starting at zero leaves no freedom in the counter annotation. -/
theorem run_eq_lift (A : FiniteGeneralizedBuchi Q Symbol) {word : Cslib.ωSequence Symbol}
    {ss : Cslib.ωSequence (Q × A.Counter)} (h : A.toFiniteBuchi.toBuchi.Run word ss) :
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
      (FiniteBuchi.mk A.initials A.successors F).toBuchi word := by
  simp only [Accepts, AcceptingRun, hf, List.mem_singleton, forall_eq]
  rfl

end FiniteGeneralizedBuchi
end KILT.Automata
