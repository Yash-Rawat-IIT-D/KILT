import KILT.Graph.Reachability

/-!
# Executable witness routes

Reachable-set computation is order independent. Returning one witness route
requires a deterministic tie breaker, supplied by an explicit complete,
duplicate-free enumeration of the state type. Each round stores at most one
route per state and extends only routes present in the preceding round.
-/

namespace KILT.Graph

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- An explicit traversal order for deterministic witness selection. -/
structure Enumeration (State : Type u) where
  states : List State
  nodup : states.Nodup
  complete : ∀ state, state ∈ states

/-- A route table stores at most one candidate route to each state. -/
abbrev RouteTable (State : Type u) := State → Option (List State)

/-- Round zero gives every seed its zero-step route. -/
def initialRouteTable (seeds : Finset State) : RouteTable State :=
  fun state => if state ∈ seeds then some [state] else none

/-- The first discovered predecessor of a target in the supplied order. -/
def predecessor? (order : Enumeration State) (successors : State → Finset State)
    (previous : RouteTable State) (target : State) : Option State :=
  order.states.find? fun source =>
    (previous source).isSome && decide (target ∈ successors source)

/-- Retain an existing route, or append the target to the first predecessor
route found in the previous round. -/
def expandRouteTable (order : Enumeration State)
    (successors : State → Finset State) (previous : RouteTable State) :
    RouteTable State :=
  fun target =>
    match previous target with
    | some route => some route
    | none =>
        match predecessor? order successors previous target with
        | none => none
        | some source => (previous source).map fun route => route ++ [target]

/-- Route tables after at most `rounds` transitions. -/
def routeTables (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) : Nat → RouteTable State
  | 0 => initialRouteTable seeds
  | rounds + 1 =>
      expandRouteTable order successors (routeTables order seeds successors rounds)

/-- Look up a cardinality-bounded witness route. -/
def route? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (target : State) : Option (List State) :=
  routeTables order seeds successors (Fintype.card State) target

omit [Fintype State] in
@[simp] theorem initialRouteTable_isSome (seeds : Finset State) (state : State) :
    (initialRouteTable seeds state).isSome = true ↔ state ∈ seeds := by
  simp [initialRouteTable]

omit [Fintype State] in
theorem predecessor_isSome_iff (order : Enumeration State)
    (successors : State → Finset State) (previous : RouteTable State)
    (target : State) :
    (predecessor? order successors previous target).isSome = true ↔
      ∃ source, (previous source).isSome = true ∧
        target ∈ successors source := by
  constructor
  · intro hsome
    cases hfind : predecessor? order successors previous target with
    | none => simp [hfind] at hsome
    | some source =>
        have hraw : order.states.find? (fun candidate =>
            (previous candidate).isSome &&
              decide (target ∈ successors candidate)) = some source := by
          simpa [predecessor?] using hfind
        have hchosen := List.find?_some hraw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hchosen
        exact ⟨source, hchosen⟩
  · rintro ⟨source, hsource, hedge⟩
    cases hfind : predecessor? order successors previous target with
    | some found => simp
    | none =>
        have hraw : order.states.find? (fun candidate =>
            (previous candidate).isSome &&
              decide (target ∈ successors candidate)) = none := by
          simpa [predecessor?] using hfind
        have hfalse := List.find?_eq_none.mp hraw source (order.complete source)
        simp [hsource, hedge] at hfalse

omit [Fintype State] in
theorem expandRouteTable_isSome_iff (order : Enumeration State)
    (successors : State → Finset State) (previous : RouteTable State)
    (target : State) :
    (expandRouteTable order successors previous target).isSome = true ↔
      (previous target).isSome = true ∨
        ∃ source, (previous source).isSome = true ∧
          target ∈ successors source := by
  cases htarget : previous target with
  | some route => simp [expandRouteTable, htarget]
  | none =>
      simp only [expandRouteTable, htarget, Option.isSome_none, Bool.false_eq_true,
        false_or]
      rw [← predecessor_isSome_iff order successors previous target]
      cases hpredecessor : predecessor? order successors previous target with
      | none => simp
      | some source =>
          have hraw : order.states.find? (fun candidate =>
              (previous candidate).isSome &&
                decide (target ∈ successors candidate)) = some source := by
            simpa [predecessor?] using hpredecessor
          have hchosen := List.find?_some hraw
          have hchosen' : (previous source).isSome = true ∧
              target ∈ successors source := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hchosen
          have hroute : (previous source).isSome = true := by
            exact hchosen'.1
          cases hsource : previous source with
          | none => simp [hsource] at hroute
          | some route => simp [hsource]

omit [Fintype State] in
/-- Table discovery agrees with set expansion at every round. -/
theorem routeTables_isSome_iff_mem_layers (order : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State)
    (rounds : Nat) (target : State) :
    (routeTables order seeds successors rounds target).isSome = true ↔
      target ∈ layers seeds successors rounds := by
  induction rounds generalizing target with
  | zero => simp [routeTables]
  | succ rounds ih =>
      rw [routeTables, expandRouteTable_isSome_iff]
      simp only [layers_succ, expand, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (hold | ⟨source, hsource, hedge⟩)
        · exact Or.inl ((ih target).mp hold)
        · exact Or.inr ⟨source, (ih source).mp hsource, hedge⟩
      · rintro (hold | ⟨source, hsource, hedge⟩)
        · exact Or.inl ((ih target).mpr hold)
        · exact Or.inr ⟨source, (ih source).mpr hsource, hedge⟩

omit [Fintype State] in
private theorem routeTables_sound (order : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State)
    {rounds : Nat} {target : State} {nodes : List State}
    (hroute : routeTables order seeds successors rounds target = some nodes) :
    ∃ source ∈ seeds,
      nodes.IsChainFromTo (Step successors) source target := by
  induction rounds generalizing target nodes with
  | zero =>
      simp only [routeTables, initialRouteTable] at hroute
      split at hroute
      next hseed =>
        cases hroute
        exact ⟨target, hseed, List.isChainFromTo_singleton⟩
      next => simp at hroute
  | succ rounds ih =>
      cases htarget : routeTables order seeds successors rounds target with
      | some prior =>
          have heq : nodes = prior := by
            simpa [routeTables, expandRouteTable, htarget] using hroute.symm
          subst nodes
          exact ih htarget
      | none =>
        cases hsource : predecessor? order successors
            (routeTables order seeds successors rounds) target with
        | none =>
            simp [routeTables, expandRouteTable, htarget, hsource] at hroute
        | some source =>
          have hraw : order.states.find? (fun candidate =>
              ((routeTables order seeds successors rounds) candidate).isSome &&
                decide (target ∈ successors candidate)) = some source := by
            simpa [predecessor?] using hsource
          have hchosen := List.find?_some hraw
          have hchosen' :
              (routeTables order seeds successors rounds source).isSome = true ∧
                target ∈ successors source := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using hchosen
          have hedge : Step successors source target := by
            change target ∈ successors source
            exact hchosen'.2
          cases hprior : routeTables order seeds successors rounds source with
          | none =>
              have : (routeTables order seeds successors rounds source).isSome =
                  true := hchosen'.1
              simp [hprior] at this
          | some prior =>
              simp only [routeTables, expandRouteTable, htarget, hsource, hprior,
                Option.map_some, Option.some.injEq] at hroute
              subst nodes
              rcases ih hprior with ⟨initial, hinitial, hchain⟩
              exact ⟨initial, hinitial, hchain.snoc hedge⟩

/-- A returned route is nonempty, starts at a seed, ends at the requested
state, and every adjacent pair is an edge. These facts are the fields of
`List.IsChainFromTo`. -/
theorem route?_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) {target : State} {nodes : List State}
    (hroute : route? order seeds successors target = some nodes) :
    ∃ source ∈ seeds,
      nodes.IsChainFromTo (Step successors) source target :=
  routeTables_sound order seeds successors hroute

/-- Lookup succeeds exactly for mathematically reachable targets. -/
@[simp] theorem route?_isSome_iff (order : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State) (target : State) :
    (route? order seeds successors target).isSome = true ↔
      Reachable seeds successors target := by
  rw [route?, routeTables_isSome_iff_mem_layers, ← mem_reachableSet_iff]
  rfl

/-- Enumeration order may alter the witness, but not reachable membership. -/
theorem route_order_independent (first second : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State) (target : State) :
    (route? first seeds successors target).isSome =
      (route? second seeds successors target).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp

end KILT.Graph
