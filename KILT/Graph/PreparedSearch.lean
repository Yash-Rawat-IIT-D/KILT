import KILT.Graph.LassoSearch

/-! Shared preparation for Boolean and accepting-witness queries. Nothing here
stores completed verdicts or makes a Boolean precheck before witness search. -/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

namespace PreparedSearch

/-- Cache the dense order and accepting mask alongside reachable adjacency. -/
structure Ready (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) where
  carrier : PreparedReachable seeds next
  vertexOrder : Enumeration carrier.graph.Vertex
  vertexOrder_eq : vertexOrder = carrier.order order
  mask : Finset carrier.graph.Vertex
  mask_eq : mask = carrier.accepting accepting

end PreparedSearch

/-- An empty problem does not need graph preparation. Its proof prevents an
arbitrary missing graph from being mistaken for a negative result. -/
inductive PreparedSearch (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) where
  | empty (reason : seeds = ∅ ∨ accepting = ∅)
  | ready (data : PreparedSearch.Ready order seeds next accepting)

def prepareSearch (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (accepting : Finset State) :
    PreparedSearch order seeds next accepting :=
  if h : seeds = ∅ ∨ accepting = ∅ then .empty h else
    let carrier := prepareReachable order seeds next
    .ready ⟨carrier, carrier.order order, rfl, carrier.accepting accepting, rfl⟩

namespace PreparedSearch
variable {order : Enumeration State} {seeds : Finset State}
variable {next : State → Finset State} {accepting : Finset State}

/-- Return queries use only the cached adjacency and accepting mask. -/
def hasAcceptingCycle : PreparedSearch order seeds next accepting → Bool
  | .empty _ => false
  | .ready data => decide (∃ q ∈ data.mask,
      data.carrier.graph.canReturn? q = true)

/-- Parent forests use the cached dense order. No original successor calls or
Boolean precheck occur during extraction. -/
def acceptingLasso? : PreparedSearch order seeds next accepting → Option (Lasso State)
  | .empty _ => none
  | .ready data =>
      (data.carrier.graph.acceptingLasso? data.vertexOrder data.carrier.initials data.mask).map
        (Lasso.map data.carrier.decode)

theorem hasAcceptingCycle_eq (problem : PreparedSearch order seeds next accepting) :
    problem.hasAcceptingCycle = Graph.hasAcceptingCycle seeds next accepting := by
  cases problem with
  | empty reason =>
    rw [Graph.hasAcceptingCycle_eq_spec]
    change false = _
    symm
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q, hq, hr, _⟩ := (hasAcceptingCycleSpec_eq_true_iff _ _ _).mp h
    rcases reason with hs | ha
    · simp [hs, Reachable] at hr
    · simp [ha] at hq
  | ready data =>
    change decide _ = _
    rw [data.mask_eq]
    exact data.carrier.hasAcceptingCycle_eq_spec accepting |>.trans
      (Graph.hasAcceptingCycle_eq_spec seeds next accepting).symm

theorem acceptingLasso?_eq (problem : PreparedSearch order seeds next accepting) :
    problem.acceptingLasso? = Graph.acceptingLasso? order seeds next accepting := by
  rw [Graph.acceptingLasso?_eq_spec]
  cases problem with
  | empty reason =>
    exact (lassoSpec?_empty order seeds next accepting reason).symm
  | ready data =>
    simp only [acceptingLasso?, data.vertexOrder_eq, data.mask_eq]
    exact data.carrier.acceptingLasso?_eq_spec order accepting

theorem acceptingLasso?_sound (problem : PreparedSearch order seeds next accepting)
    {l : Lasso State} (h : problem.acceptingLasso? = some l) :
    l.Valid seeds next ∧ l.entry ∈ accepting := by
  rw [problem.acceptingLasso?_eq] at h
  exact Graph.acceptingLasso?_sound _ _ _ _ h

theorem acceptingLasso?_isSome_iff (problem : PreparedSearch order seeds next accepting) :
    problem.acceptingLasso?.isSome = true ↔ problem.hasAcceptingCycle = true := by
  rw [problem.acceptingLasso?_eq, problem.hasAcceptingCycle_eq]
  exact Graph.acceptingLasso?_isSome_iff _ _ _ _

end PreparedSearch
end KILT.Graph
