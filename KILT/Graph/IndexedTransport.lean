import KILT.Graph.IndexedParents

/-! Exact route selection under reachable-subgraph reindexing. -/
namespace KILT.Graph.PreparedReachable
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]
variable {seeds : Finset State} {next : State → Finset State}

theorem index?_none_iff (p : PreparedReachable seeds next) (s : State) :
    p.index? s = none ↔ ¬ Reachable seeds next s := by
  constructor
  · intro hn hr
    obtain ⟨i, hi⟩ := (p.exists_decode_iff s).mpr hr
    have hs := (p.index?_eq_some_iff s i).mpr hi
    simp [hn] at hs
  · intro hn
    cases hi : p.index? s with
    | none => rfl
    | some i =>
      have hd := (p.index?_eq_some_iff s i).mp hi
      exact (hn (hd ▸ p.decode_reachable i)).elim

def queryInitials (p : PreparedReachable seeds next) (query : Finset State) : Finset p.graph.Vertex :=
  Finset.univ.filter (fun i => p.decode i ∈ query)

theorem outside_routes (p : PreparedReachable seeds next) (original : Enumeration State)
    (query : Finset State) (covered : ∀ s ∈ query, Reachable seeds next s)
    (n : Nat) (s : State) (hs : p.index? s = none) :
    routeTables original query next n s = none := by
  cases hr : routeTables original query next n s with
  | none => rfl
  | some path =>
    have hm := (routeTables_isSome_iff_mem_layers original query next n s).mp (by simp [hr])
    obtain ⟨start, hstart, hpath⟩ := mem_layers_reachable hm
    obtain ⟨initial, hinitial, hprefix⟩ := covered start hstart
    exact ((p.index?_none_iff s).mp hs ⟨initial, hinitial, hprefix.trans hpath⟩).elim

theorem predecessor_transport (p : PreparedReachable seeds next) (original : Enumeration State)
    (localRoutes : RouteTable p.graph.Vertex) (originalRoutes : RouteTable State)
    (represented : ∀ i, (localRoutes i).map (List.map p.decode) = originalRoutes (p.decode i))
    (outside : ∀ s, p.index? s = none → originalRoutes s = none)
    (target : p.graph.Vertex) :
    (predecessor? (p.order original) p.graph.successors localRoutes target).map p.decode =
      predecessor? original next originalRoutes (p.decode target) := by
  let predicate := fun i => (localRoutes i).isSome && decide (target ∈ p.graph.successors i)
  let oldPredicate := fun s => (originalRoutes s).isSome && decide (p.decode target ∈ next s)
  have predicates : (fun s => (p.index? s).any predicate) = oldPredicate := by
    funext s
    cases hi : p.index? s with
    | none => simp [hi, oldPredicate, outside s hi]
    | some i =>
      have hd := (p.index?_eq_some_iff s i).mp hi
      have hr := congrArg Option.isSome (represented i)
      simp only [Option.isSome_map] at hr
      simp only [hi, Option.any_some]
      change ((localRoutes i).isSome && decide (target ∈ p.graph.successors i)) =
        ((originalRoutes s).isSome && decide (p.decode target ∈ next s))
      have he : decide (target ∈ p.graph.successors i) = decide (p.decode target ∈ next s) := by
        apply decide_eq_decide.mpr
        have he := p.step_decode i target
        change (target ∈ p.graph.successors i ↔ p.decode target ∈ next (p.decode i)) at he
        simpa only [hd] using he
      rw [he, hr, hd]
  simp only [predecessor?, order, List.find?_filterMap]
  change ((original.states.find? (fun s => (p.index? s).any predicate)).bind p.index?).map p.decode =
    original.states.find? oldPredicate
  rw [predicates]
  cases hf : original.states.find? oldPredicate with
  | none => simp
  | some s =>
    have hchosen := List.find?_some hf
    have hr : (originalRoutes s).isSome = true := (Bool.and_eq_true_iff.mp hchosen).1
    cases hi : p.index? s with
    | none => simp [outside s hi] at hr
    | some i =>
      have hd := (p.index?_eq_some_iff s i).mp hi
      simp [hi, hd]

theorem routeTables_transport (p : PreparedReachable seeds next) (original : Enumeration State)
    (query : Finset State) (covered : ∀ s ∈ query, Reachable seeds next s)
    (n : Nat) (target : p.graph.Vertex) :
    (routeTables (p.order original) (p.queryInitials query) p.graph.successors n target).map
      (List.map p.decode) = routeTables original query next n (p.decode target) := by
  induction n generalizing target with
  | zero => simp [routeTables, initialRouteTable, queryInitials]
  | succ n ih =>
    let localRoutes := routeTables (p.order original) (p.queryInitials query) p.graph.successors n
    let originalRoutes := routeTables original query next n
    have pred := p.predecessor_transport original localRoutes originalRoutes ih
      (p.outside_routes original query covered n) target
    change (expandRouteTable (p.order original) p.graph.successors localRoutes target).map
      (List.map p.decode) = expandRouteTable original next originalRoutes (p.decode target)
    cases ht : localRoutes target with
    | some path =>
      have hi := (ih target).symm
      change originalRoutes (p.decode target) = (localRoutes target).map (List.map p.decode) at hi
      have ho : originalRoutes (p.decode target) = some (path.map p.decode) := by simpa [ht] using hi
      simp [expandRouteTable, ht, ho]
    | none =>
      have hi := (ih target).symm
      change originalRoutes (p.decode target) = (localRoutes target).map (List.map p.decode) at hi
      have ho : originalRoutes (p.decode target) = none := by simpa [ht] using hi
      cases hf : predecessor? (p.order original) p.graph.successors localRoutes target with
      | none =>
        have hf' : predecessor? original next originalRoutes (p.decode target) = none := by
          simpa [hf] using pred.symm
        simp [expandRouteTable, ht, ho, hf, hf']
      | some source =>
        have hf' : predecessor? original next originalRoutes (p.decode target) = some (p.decode source) := by
          simpa [hf] using pred.symm
        have hs := ih source
        change (localRoutes source).map (List.map p.decode) = originalRoutes (p.decode source) at hs
        cases hr : localRoutes source with
        | none =>
          have hs' : originalRoutes (p.decode source) = none := by simpa [hr] using hs.symm
          simp [expandRouteTable, ht, ho, hf, hf', hr, hs']
        | some path =>
          have hs' : originalRoutes (p.decode source) = some (path.map p.decode) := by simpa [hr] using hs.symm
          simp [expandRouteTable, ht, ho, hf, hf', hr, hs', List.map_append]

end KILT.Graph.PreparedReachable

namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

/-- No route can change once the cardinality-bounded discovered set is closed. -/
theorem routeTables_fixed_at_card (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) :
    expandRouteTable order next (routeTables order seeds next (Fintype.card State)) =
      routeTables order seeds next (Fintype.card State) := by
  funext target
  cases hp : routeTables order seeds next (Fintype.card State) target with
  | some path => simp [expandRouteTable, hp]
  | none =>
    cases hn : expandRouteTable order next (routeTables order seeds next (Fintype.card State)) target with
    | none => rfl
    | some path =>
      have hs : (routeTables order seeds next (Fintype.card State + 1) target).isSome = true := by
        simp [routeTables, hn]
      have hm := (routeTables_isSome_iff_mem_layers _ _ _ _ _).mp hs
      rw [layers_stable_at_card] at hm
      have hi := (routeTables_isSome_iff_mem_layers order seeds next (Fintype.card State) target).mpr hm
      simp [hp] at hi

theorem routeTables_after_card (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (n : Nat) (bound : Fintype.card State ≤ n) :
    routeTables order seeds next n = route? order seeds next := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le bound
  induction k with
  | zero => simp only [Nat.add_zero]; rfl
  | succ k ih =>
    have hn : Fintype.card State + (k + 1) = (Fintype.card State + k) + 1 := by omega
    have ih' := ih (by omega)
    rw [hn, routeTables, ih']
    exact routeTables_fixed_at_card order seeds next

theorem PreparedReachable.route?_transport {seeds : Finset State} {next : State → Finset State}
    (p : PreparedReachable seeds next) (original : Enumeration State)
    (query : Finset State) (covered : ∀ s ∈ query, Reachable seeds next s)
    (target : p.graph.Vertex) :
    (route? (p.order original) (p.queryInitials query) p.graph.successors target).map
      (List.map p.decode) = route? original query next (p.decode target) := by
  have bound : Fintype.card p.graph.Vertex ≤ Fintype.card State := by
    have hn := List.Nodup.length_le_card p.nodup
    simpa only [Fintype.card_fin, Array.length_toList, p.states_size] using hn
  have h := p.routeTables_transport original query covered (Fintype.card State) target
  rw [routeTables_after_card _ _ _ _ bound] at h
  exact h

end KILT.Graph
