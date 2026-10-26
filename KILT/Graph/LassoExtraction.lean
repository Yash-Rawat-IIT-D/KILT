import KILT.Graph.RouteTransport
import KILT.Graph.Parents
import KILT.Graph.Specification.Lasso

/-! Accepting lasso extraction with parent storage and exact route transport. -/
namespace KILT.Graph

namespace FiniteGraph

private def parentCandidate? (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds accepting : Finset g.Vertex) (stems : ParentForest g order seeds) (q : g.Vertex) : Option (Lasso g.Vertex) :=
  if q ∈ accepting then
    if stems.reached q then
      let returns := g.parentsTo order (g.successors q) q
      if returns.reached then
        (stems.route? q).bind fun stem =>
          returns.route?.map fun back =>
            ⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩
      else none
    else none
  else none

/-- Keep only parent forests during expansion; reconstruct lists for the first
successful candidate. This synchronous implementation is the storage reference. -/
def acceptingLasso? (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds accepting : Finset g.Vertex) : Option (Lasso g.Vertex) :=
  let stems := g.parentForest order seeds
  order.states.findSome? (parentCandidate? g order seeds accepting stems)

theorem acceptingLasso?_eq_spec (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds accepting : Finset g.Vertex) :
    g.acceptingLasso? order seeds accepting =
      Graph.lassoSpec? order seeds g.successors accepting := by
  rw [Graph.lassoSpec?_eq_findSome]
  dsimp only [acceptingLasso?]
  apply congrArg (fun f => order.states.findSome? f)
  funext q
  let stems := g.parentForest order seeds
  let returns := g.parentsTo order (g.successors q) q
  have hs := stems.route?_eq_spec q
  have hr := returns.route?_eq_spec
  have hsk := stems.reached_eq q
  have hrk := returns.reached_eq
  change parentCandidate? g order seeds accepting stems q = _
  unfold parentCandidate?
  change (if q ∈ accepting then if stems.reached q then
    if returns.reached then
      (stems.route? q).bind (fun stem =>
        returns.route?.map (fun back =>
          (⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩ : Lasso g.Vertex)))
    else none else none else none) = _
  rw [hs, hr, hsk, hrk]
  split
  · cases routeSpec? order seeds g.successors q <;>
      cases routeSpec? order (g.successors q) g.successors q <;> rfl
  · rfl

end FiniteGraph

private theorem findSome_filterMap_map {α β γ δ : Type*} (xs : List α)
    (index : α → Option β) (candidate : β → Option γ) (decode : γ → δ) :
    ((xs.filterMap index).findSome? candidate).map decode =
      xs.findSome? (fun a => (index a).bind (fun b => (candidate b).map decode)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases hi : index a with
    | none => simpa [hi] using ih
    | some b =>
      cases hc : candidate b with
      | none => simpa [hi, hc] using ih
      | some c => simp [hi, hc]

namespace PreparedReachable
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]
variable {seeds : Finset State} {next : State → Finset State}

theorem initials_eq_query (p : PreparedReachable seeds next) :
    p.initials = p.queryInitials seeds := by
  ext i
  simp [queryInitials]

theorem successors_eq_query (p : PreparedReachable seeds next) (i : p.graph.Vertex) :
    p.graph.successors i = p.queryInitials (next (p.decode i)) := by
  ext j
  exact (p.step_decode i j).trans (by simp [Step, queryInitials])

/-- Dense parent forests, mapped back to the caller's original states. -/
def acceptingLasso? (p : PreparedReachable seeds next) (original : Enumeration State)
    (accepting : Finset State) : Option (Lasso State) :=
  (p.graph.acceptingLasso? (p.order original) p.initials (p.accepting accepting)).map (Lasso.map p.decode)

theorem acceptingLasso?_eq_spec (p : PreparedReachable seeds next)
    (original : Enumeration State) (accepting : Finset State) :
    p.acceptingLasso? original accepting = Graph.lassoSpec? original seeds next accepting := by
  unfold acceptingLasso?
  rw [FiniteGraph.acceptingLasso?_eq_spec,
    Graph.lassoSpec?_eq_findSome, Graph.lassoSpec?_eq_findSome]
  let localCandidate := fun q : p.graph.Vertex =>
    if q ∈ p.accepting accepting then
      (routeSpec? (p.order original) p.initials p.graph.successors q).bind fun stem =>
        (routeSpec? (p.order original) (p.graph.successors q) p.graph.successors q).map fun back =>
          (⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩ : Lasso p.graph.Vertex)
    else none
  let originalCandidate := fun s : State =>
    if s ∈ accepting then
      (routeSpec? original seeds next s).bind fun stem =>
        (routeSpec? original (next s) next s).map fun back =>
          (⟨stem.dropLast, s :: back.dropLast, List.cons_ne_nil _ _⟩ : Lasso State)
    else none
  change ((original.states.filterMap p.index?).findSome? localCandidate).map (Lasso.map p.decode) =
    original.states.findSome? originalCandidate
  rw [findSome_filterMap_map]
  apply congrArg (fun f => original.states.findSome? f)
  funext s
  cases hi : p.index? s with
  | none =>
    have hs : routeSpec? original seeds next s = none :=
      p.outside_routes original seeds (fun s hs => ⟨s, hs, .refl⟩) (Fintype.card State) s hi
    simp [hi, originalCandidate, hs]
  | some q =>
    have hd := (p.index?_eq_some_iff s q).mp hi
    have hs := p.routeSpec?_transport original seeds (fun s hs => ⟨s, hs, .refl⟩) q
    rw [← p.initials_eq_query] at hs
    have covered : ∀ t ∈ next (p.decode q), Reachable seeds next t := by
      intro t ht
      obtain ⟨start, hstart, path⟩ := p.decode_reachable q
      exact ⟨start, hstart, path.tail ht⟩
    have hr := p.routeSpec?_transport original (next (p.decode q)) covered q
    rw [← p.successors_eq_query q] at hr
    cases hd
    simp only [hi, Option.bind_some]
    by_cases ha : p.decode q ∈ accepting
    · simp only [localCandidate, originalCandidate, mem_accepting, ha, ↓reduceIte]
      cases ht : routeSpec? (p.order original) p.initials p.graph.successors q with
      | none =>
        have hs' : routeSpec? original seeds next (p.decode q) = none := by simpa [ht] using hs.symm
        simp [ht, hs']
      | some stem =>
        have hs' : routeSpec? original seeds next (p.decode q) = some (stem.map p.decode) := by
          simpa [ht] using hs.symm
        cases hb : routeSpec? (p.order original) (p.graph.successors q) p.graph.successors q with
        | none =>
          have hr' : routeSpec? original (next (p.decode q)) next (p.decode q) = none := by simpa [hb] using hr.symm
          simp [ht, hs', hb, hr']
        | some back =>
          have hr' : routeSpec? original (next (p.decode q)) next (p.decode q) = some (back.map p.decode) := by
            simpa [hb] using hr.symm
          simp [ht, hs', hb, hr', Lasso.map, List.map_dropLast]
    · simp [localCandidate, originalCandidate, ha]

end PreparedReachable
end KILT.Graph
