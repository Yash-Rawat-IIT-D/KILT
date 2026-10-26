import KILT.Graph.RouteTransport
import KILT.Graph.Frontier

/-! Public route lookup reconstructs one parent chain. Its specification retains
finite-level enumeration tie-breaking without executing a route-table backend. -/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

def route? (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (target : State) : Option (List State) :=
  let p := prepareReachable order seeds next
  (p.index? target).bind fun i =>
    (((FiniteGraph.Parents.initial p.graph p.initials).frontierSearch
      (p.order order) (some i) p.graph.size 0).unwind (p.graph.size + 1) i []).map (List.map p.decode)

theorem route?_eq_spec (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (target : State) :
    route? order seeds next target = routeSpec? order seeds next target := by
  let p := prepareReachable order seeds next
  change (p.index? target).bind _ = _
  cases hi : p.index? target with
  | none =>
    simp only [Option.bind_none]
    exact (p.outside_routes order seeds (fun s hs => ⟨s, hs, .refl⟩)
      (Fintype.card State) target hi).symm
  | some i =>
    have hd := (p.index?_eq_some_iff target i).mp hi
    simp only [Option.bind_some]
    rw [FiniteGraph.Parents.frontierTarget_eq]
    change (FiniteGraph.parentRouteFast? p.graph (p.order order) p.initials i).map
      (List.map p.decode) = _
    rw [FiniteGraph.parentRouteFast?_eq]
    have ht := p.routeSpec?_transport order seeds (fun s hs => ⟨s, hs, .refl⟩) i
    have hinitial : p.queryInitials seeds = p.initials := by
      ext j
      simp [PreparedReachable.queryInitials]
    rw [hinitial] at ht
    simpa [hd] using ht

@[simp] theorem route?_isSome_iff (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (target : State) :
    (route? order seeds next target).isSome = true ↔ Reachable seeds next target := by
  rw [route?_eq_spec, routeSpec?_isSome_iff]

theorem route?_sound (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) {target : State} {nodes : List State}
    (h : route? order seeds next target = some nodes) :
    ∃ start ∈ seeds, nodes.IsChainFromTo (Step next) start target := by
  rw [route?_eq_spec] at h
  exact routeSpec?_sound order seeds next h

theorem route_order_independent (first second : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (target : State) :
    (route? first seeds next target).isSome = (route? second seeds next target).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [route?_isSome_iff, route?_isSome_iff]

end KILT.Graph
