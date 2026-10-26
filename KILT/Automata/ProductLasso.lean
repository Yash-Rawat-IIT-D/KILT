import KILT.Automata.Product
import KILT.Graph.PreparedSearch

/-! Prepared products and actual-trace projection, also for partial models and
handwritten monitors. Formula checking adds seriality only at its own boundary. -/
namespace KILT.FiniteKripke
open LTL Automata Cslib.Automata
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

abbrev PreparedProduct (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :=
  Graph.PreparedSearch (order.product automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (productAccepting A)

/-- A reachable product vertex is accepting exactly when its automaton state is. -/
theorem productAcceptingMask_eq (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (p : Graph.PreparedReachable (M.productInitials A) (M.productSuccessors A)) :
    (Finset.univ.filter fun i : p.graph.Vertex => (p.decode i).2 ∈ A.accepting) =
      p.accepting (productAccepting A) := by
  ext i
  simp [Graph.PreparedReachable.accepting, productAccepting]

/-- Prepare product adjacency, acceptance and order once for either kind of query. -/
def prepareProduct (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    M.PreparedProduct A order automatonOrder := by
  if hi : A.initials = ∅ then
    exact .empty (Or.inl (by simp [productInitials, hi]))
  else if ha : A.accepting = ∅ then
    exact .empty (Or.inr (by simp [productAccepting, ha]))
  else
    let carrier := Graph.prepareReachable (order.product automatonOrder)
      (M.productInitials A) (M.productSuccessors A)
    let mask := Finset.univ.filter (fun i : carrier.graph.Vertex => (carrier.decode i).2 ∈ A.accepting)
    have hm : mask = carrier.accepting (productAccepting A) :=
      M.productAcceptingMask_eq A carrier
    exact .ready ⟨carrier, carrier.order (order.product automatonOrder), rfl, mask, hm⟩

theorem prepareProduct_hasAcceptingCycle_eq (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    (M.prepareProduct A order automatonOrder).hasAcceptingCycle = M.hasAcceptedPath A :=
  Graph.PreparedSearch.hasAcceptingCycle_eq _

def acceptedLasso? (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    Option (Graph.Lasso (State × Q)) :=
  (M.prepareProduct A order automatonOrder).acceptingLasso?

theorem acceptedLasso?_eq_graph (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    M.acceptedLasso? A order automatonOrder =
      Graph.acceptingLasso? (order.product automatonOrder)
        (M.productInitials A) (M.productSuccessors A) (productAccepting A) :=
  Graph.PreparedSearch.acceptingLasso?_eq _

theorem acceptedLasso?_valid (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q)
    {l : Graph.Lasso (State × Q)} (h : M.acceptedLasso? A order automatonOrder = some l) :
    l.Valid (M.productInitials A) (M.productSuccessors A) ∧ l.entry ∈ productAccepting A :=
  (M.prepareProduct A order automatonOrder).acceptingLasso?_sound h

/-- Replay the actual product witness as a system path. -/
def productLassoPath (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) : M.toKripke.Path where
  states := l.sequence.map Prod.fst
  valid i := (Finset.mem_product.mp (h.step i)).1

@[simp] theorem productLassoPath_states (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) :
    (M.productLassoPath A l h).states = (l.map Prod.fst).sequence :=
  (l.map_sequence Prod.fst).symm

theorem productLassoPath_initial (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A)) :
    (M.productLassoPath A l h).IsInitial :=
  (Finset.mem_product.mp h.initial).1

theorem productLassoPath_accepts (M : FiniteKripke State AP)
    (A : FiniteBuchi Q (Valuation AP)) (l : Graph.Lasso (State × Q))
    (h : l.Valid (M.productInitials A) (M.productSuccessors A))
    (ha : l.entry ∈ productAccepting A) :
    ωAcceptor.Accepts A.toCSLib (M.productLassoPath A l h).word := by
  have hr := (M.product_run_iff A (l.sequence.map Prod.fst) (l.sequence.map Prod.snd)).mp
    (show (l.sequence.map Prod.fst 0, l.sequence.map Prod.snd 0) ∈ M.productInitials A ∧
      ∀ i, (l.sequence.map Prod.fst (i + 1), l.sequence.map Prod.snd (i + 1)) ∈
        M.productSuccessors A (l.sequence.map Prod.fst i, l.sequence.map Prod.snd i) from
      by simpa only [Cslib.ωSequence.get_map, Prod.mk.eta, Graph.Step] using And.intro h.initial h.step)
  refine ⟨l.sequence.map Prod.snd, hr.2.2, ?_⟩
  have hacc : l.entry.2 ∈ A.accepting := (Finset.mem_product.mp ha).2
  exact l.frequently_entry.mono fun _ heq => by
    change (l.sequence _).2 ∈ A.accepting
    rw [heq]
    exact hacc

/-- A returned witness's own projection is initial and accepted. -/
theorem acceptedLasso?_sound (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q)
    {l : Graph.Lasso (State × Q)} (h : M.acceptedLasso? A order automatonOrder = some l) :
    let hv := (M.acceptedLasso?_valid A order automatonOrder h).1
    (M.productLassoPath A l hv).IsInitial ∧
      ωAcceptor.Accepts A.toCSLib (M.productLassoPath A l hv).word := by
  exact ⟨M.productLassoPath_initial A l _, M.productLassoPath_accepts A l _
    (M.acceptedLasso?_valid A order automatonOrder h).2⟩

theorem acceptedLasso?_isSome_iff (M : FiniteKripke State AP) (A : FiniteBuchi Q (Valuation AP))
    (order : Graph.Enumeration State) (automatonOrder : Graph.Enumeration Q) :
    (M.acceptedLasso? A order automatonOrder).isSome = true ↔ M.hasAcceptedPath A = true := by
  change (M.prepareProduct A order automatonOrder).acceptingLasso?.isSome = true ↔ _
  rw [Graph.PreparedSearch.acceptingLasso?_isSome_iff, prepareProduct_hasAcceptingCycle_eq]

end KILT.FiniteKripke
