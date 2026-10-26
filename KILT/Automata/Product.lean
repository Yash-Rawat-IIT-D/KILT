import KILT.Automata.FiniteBuchi
import KILT.Automata.Kripke
import KILT.Kripke.Finite
import KILT.Graph.Buchi

/-!
# Finite Kripke/property-automaton product

The automaton consumes the source state's valuation on each product edge.
The product is graph data, so an empty automaton initial set is allowed.
Generic accepted-path search handles partial graphs. The public property
checker requires seriality and a proved violation-language specification.
-/
namespace KILT.FiniteKripke
open Automata Cslib Cslib.Automata
open Filter
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

def productInitials (M : FiniteKripke State AP) (A : FiniteBuchi Q (LTL.Valuation AP)) :
    Finset (State × Q) := M.initials ×ˢ A.initials

def productSuccessors (M : FiniteKripke State AP) (A : FiniteBuchi Q (LTL.Valuation AP))
    (current : State × Q) : Finset (State × Q) :=
  M.successors current.1 ×ˢ A.successors current.2 (M.label current.1)

def productAccepting (A : FiniteBuchi Q (LTL.Valuation AP)) : Finset (State × Q) :=
  Finset.univ ×ˢ A.accepting

/-- Product edges and starts are precisely compatible system/automaton runs. -/
theorem product_run_iff (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (LTL.Valuation AP))
    (ss : ωSequence State) (qs : ωSequence Q) :
    ((ss 0, qs 0) ∈ M.productInitials A ∧
      ∀ i, (ss (i + 1), qs (i + 1)) ∈ M.productSuccessors A (ss i, qs i)) ↔
    M.toKripke.initial (ss 0) ∧
      (∀ i, M.toKripke.step (ss i) (ss (i + 1))) ∧
      A.toCSLib.Run (ss.map M.label) qs := by
  constructor
  · rintro ⟨hstart, hstep⟩
    have hstarts := Finset.mem_product.mp hstart
    exact ⟨hstarts.1, fun i => (Finset.mem_product.mp (hstep i)).1,
      ⟨hstarts.2, fun i => (Finset.mem_product.mp (hstep i)).2⟩⟩
  · rintro ⟨hstart, hstep, hrun⟩
    exact ⟨Finset.mem_product.mpr ⟨hstart, hrun.start⟩,
      fun i => Finset.mem_product.mpr ⟨hstep i, hrun.trans i⟩⟩

/-- Decide existence of an initial path accepted by the supplied automaton. -/
def hasAcceptedPath (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (LTL.Valuation AP)) : Bool :=
  Graph.hasAcceptingCycle (M.productInitials A) (M.productSuccessors A) (productAccepting A)

theorem hasAcceptedPath_eq_true_iff (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (LTL.Valuation AP)) :
    M.hasAcceptedPath A = true ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ ωAcceptor.Accepts A.toCSLib p.word := by
  rw [hasAcceptedPath, Graph.hasAcceptingCycle_eq_true_iff_run]
  constructor
  · rintro ⟨ss, hstart, hstep, hacc⟩
    let p : M.toKripke.Path :=
      ⟨ss.map Prod.fst, fun i => (Finset.mem_product.mp (hstep i)).1⟩
    refine ⟨p, (Finset.mem_product.mp hstart).1, ss.map Prod.snd,
      ⟨(Finset.mem_product.mp hstart).2,
        fun i => (Finset.mem_product.mp (hstep i)).2⟩, ?_⟩
    simpa only [productAccepting, Finset.mem_product, Finset.mem_univ, true_and, FiniteBuchi.toCSLib_accept,
      Cslib.ωSequence.get_map, Cslib.ωSequence.get_zip] using hacc
  · rintro ⟨p, hp, qs, hrun, hacc⟩
    refine ⟨p.states.zip Prod.mk qs, Finset.mem_product.mpr ⟨hp, hrun.start⟩,
      fun i => Finset.mem_product.mpr ⟨p.valid i, hrun.trans i⟩, ?_⟩
    simpa only [productAccepting, Finset.mem_product, Finset.mem_univ, true_and, FiniteBuchi.toCSLib_accept,
      Cslib.ωSequence.get_map, Cslib.ωSequence.get_zip] using hacc

/-- Check a property against a supplied violation automaton. Seriality is an
explicit library precondition; the backend itself permits deadlocks. -/
def checkAgainst (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (LTL.Valuation AP)) (_serial : M.toKripke.Serial) : Bool :=
  !M.hasAcceptedPath A

/-- Absence of accepted violations is universal system satisfaction. This is
conditional on the supplied automaton's language theorem, not a translator. -/
theorem checkAgainst_correct (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (LTL.Valuation AP)) (serial : M.toKripke.Serial)
    (formula : LTL.Formula AP)
    (violations : ∀ word, ωAcceptor.Accepts A.toCSLib word ↔ ¬ LTL.WordSat word formula) :
    M.checkAgainst A serial = true ↔ M.toKripke.Satisfies formula := by
  classical
  have hzero : M.hasAcceptedPath A = false ↔
      ¬ ∃ p : M.toKripke.Path, p.IsInitial ∧ ωAcceptor.Accepts A.toCSLib p.word := by
    rw [Bool.eq_false_iff]
    exact not_congr (hasAcceptedPath_eq_true_iff M A)
  rw [checkAgainst, Bool.not_eq_true', hzero]
  constructor
  · intro h p hp
    by_contra hnot
    exact h ⟨p, hp, (violations p.word).mpr hnot⟩
  · intro h ⟨p, hp, haccept⟩
    exact (violations p.word).mp haccept (h p hp)

end KILT.FiniteKripke
