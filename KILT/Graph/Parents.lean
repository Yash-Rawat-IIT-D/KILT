import KILT.Graph.Internal.Frontier

/-!
# Production parent searches

`parentForest` computes complete reachability information; `parentsTo` may stop
as soon as its target is found. Only the former supports arbitrary route
queries. Both fix initialization, level and fuel internally and preserve the
reference enumeration tie-breaking. Raw rounds and their refinement lemmas
live under `FiniteGraph.Internal`, not the supported search API.
-/
namespace KILT.Graph.FiniteGraph

/-- A complete forest, with proof that its storage is the canonical full search. -/
structure ParentForest (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) where
  storage : Internal.Parents g
  storage_eq : storage = Internal.Parents.frontierForest g order seeds

/-- Completed parent information for all reachable vertices. -/
def parentForest (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) : ParentForest g order seeds :=
  ⟨Internal.Parents.frontierForest g order seeds, rfl⟩

/-- Reconstruct just the requested route from a completed forest. -/
def ParentForest.route? {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} (p : ParentForest g order seeds) (target : g.Vertex) :
    Option (List g.Vertex) := p.storage.unwind (g.size + 1) target []

theorem ParentForest.route?_eq_spec {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} (p : ParentForest g order seeds) (target : g.Vertex) :
    p.route? target = routeSpec? order seeds g.successors target := by
  unfold route?
  rw [p.storage_eq, Internal.Parents.frontierForest_eq]
  exact Internal.Parents.forest_unwind g order seeds target

/-- A target-only search result. It is not a complete reachability closure. -/
structure TargetParents (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) where
  storage : Internal.Parents g
  storage_eq : storage = (Internal.Parents.initial g seeds).frontierSearch
    order (some target) g.size 0

/-- Stop at finalized target discovery or exhaustion. Earlier-level parents
remain stored, but the result does not expose arbitrary-target route lookup. -/
def parentsTo (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) : TargetParents g order seeds target :=
  ⟨(Internal.Parents.initial g seeds).frontierSearch order (some target) g.size 0, rfl⟩

def TargetParents.route? {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} {target : g.Vertex} (p : TargetParents g order seeds target) :
    Option (List g.Vertex) := p.storage.unwind (g.size + 1) target []

theorem TargetParents.route?_eq_spec {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} {target : g.Vertex} (p : TargetParents g order seeds target) :
    p.route? = routeSpec? order seeds g.successors target := by
  unfold route?
  rw [p.storage_eq, Internal.Parents.frontierTarget_eq]
  exact Internal.parentRouteFast?_eq g order seeds target

/-- Constant-time discovery test without reconstructing a route. -/
def ParentForest.reached {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} (p : ParentForest g order seeds) (target : g.Vertex) : Bool :=
  (p.storage.get target).depth.isSome

theorem ParentForest.reached_eq {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} (p : ParentForest g order seeds) (target : g.Vertex) :
    p.reached target = (routeSpec? order seeds g.successors target).isSome := by
  unfold reached
  rw [p.storage_eq, Internal.Parents.frontierForest_eq]
  exact (Internal.Parents.forest g order seeds).isSome_iff
    (Internal.Parents.forest_represents g order seeds) target

def TargetParents.reached {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} {target : g.Vertex} (p : TargetParents g order seeds target) : Bool :=
  (p.storage.get target).depth.isSome

theorem TargetParents.reached_eq {g : FiniteGraph} {order : Enumeration g.Vertex}
    {seeds : Finset g.Vertex} {target : g.Vertex} (p : TargetParents g order seeds target) :
    p.reached = (routeSpec? order seeds g.successors target).isSome := by
  unfold reached
  rw [p.storage_eq, Internal.Parents.frontierTarget_eq]
  exact Internal.Parents.target_isSome g order seeds target

/-- One target route, without constructing routes for other vertices. -/
def parentRoute? (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) : Option (List g.Vertex) :=
  (g.parentsTo order seeds target).route?

theorem parentRoute?_eq_spec (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    g.parentRoute? order seeds target = routeSpec? order seeds g.successors target :=
  (g.parentsTo order seeds target).route?_eq_spec

/-- Exact return route with deadlock/self-loop shortcuts, preserving seed-route selection. -/
def returnRoute? (g : FiniteGraph) (order : Enumeration g.Vertex) (q : g.Vertex) :
    Option (List g.Vertex) :=
  if (g.row q).size = 0 then none else
    if g.edge q q then some [q] else g.parentRoute? order (g.successors q) q

theorem returnRoute?_eq_spec (g : FiniteGraph) (order : Enumeration g.Vertex) (q : g.Vertex) :
    returnRoute? g order q = routeSpec? order (g.successors q) g.successors q := by
  unfold returnRoute?
  split
  next he =>
    have hs : g.successors q = ∅ := by
      simp [successors, Array.eq_empty_of_size_eq_zero he]
    rw [hs]
    symm
    cases hr : routeSpec? order ∅ g.successors q with
    | none => rfl
    | some route =>
      have h := (routeSpec?_isSome_iff order ∅ g.successors q).mp (by simp [hr])
      simp [Reachable] at h
  next =>
    split
    next he =>
      have hq : q ∈ g.successors q := by simpa [edge_eq_decide] using he
      have h := routeRounds_retains order g.successors (Fintype.card g.Vertex)
        (initialRouteTable (g.successors q)) q [q] (by simp [initialRouteTable, hq])
      simpa [routeRounds_initial, routeSpec?] using h.symm
    next => exact parentRoute?_eq_spec g order (g.successors q) q
end KILT.Graph.FiniteGraph
