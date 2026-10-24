import KILT.Graph.StoredRoutes

/-!
# Refinements for finite graph search

Full closure stops at stability; a target query may stop sooner. The original
cardinality-bounded layers and route tables remain the mathematical references.
Caches are local data: lookup has exactly the supplied graph's successors.
-/
namespace KILT.Graph
universe u
variable {State : Type u} [DecidableEq State]

/-- A complete successor table, prepared once per search invocation. -/
def prepareSuccessors (order : Enumeration State) (successors : State → Finset State) :=
  materialize order successors

@[simp] theorem prepareSuccessors_lookup (order : Enumeration State)
    (successors : State → Finset State) (s : State) :
    tableLookup ∅ (prepareSuccessors order successors) s = successors s :=
  tableLookup_materialize _ _ _ _

/-- Order-independent successor rows for callers supplying only Fintype. -/
def prepareSuccessorSet [Fintype State] (successors : State → Finset State) :
    Finset (State × Finset State) := Finset.univ.image fun s => (s, successors s)

/-- Missing rows contribute no edges; a prepared complete cache has one row per key. -/
def successorSetLookup (rows : Finset (State × Finset State)) (s : State) : Finset State :=
  rows.biUnion fun row => if row.1 = s then row.2 else ∅

@[simp] theorem prepareSuccessorSet_lookup [Fintype State]
    (successors : State → Finset State) (s : State) :
    successorSetLookup (prepareSuccessorSet successors) s = successors s := by
  ext t
  simp only [successorSetLookup, prepareSuccessorSet, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨r, edges⟩, ⟨q, heq⟩, ht⟩
    cases heq
    split at ht
    next h =>
      have hrs : r = s := h
      simpa [hrs] using ht
    next => simp at ht
  · intro ht
    exact ⟨(s, successors s), ⟨s, rfl⟩, by simpa using ht⟩

/-- Forward iteration, with the same expansion as `layers`. -/
def expandRounds (successors : State → Finset State) : Nat → Finset State → Finset State
  | 0, reached => reached
  | n + 1, reached => expandRounds successors n (expand successors reached)

theorem expandRounds_eq_layers (successors : State → Finset State) (n : Nat)
    (seeds : Finset State) : expandRounds successors n seeds = layers seeds successors n := by
  induction n generalizing seeds with
  | zero => rfl
  | succ n ih =>
    rw [expandRounds, ih]
    have comm : ∀ k, layers (expand successors seeds) successors k =
        expand successors (layers seeds successors k) := by
      intro k
      induction k with
      | zero => rfl
      | succ k hk => simpa only [layers_succ] using congrArg (expand successors) hk
    exact comm n

theorem expandRounds_fixed (successors : State → Finset State) (n : Nat)
    (reached : Finset State) (h : expand successors reached = reached) :
    expandRounds successors n reached = reached := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [expandRounds, h] using ih

theorem subset_expandRounds (successors : State → Finset State) (n : Nat)
    (reached : Finset State) : reached ⊆ expandRounds successors n reached := by
  induction n generalizing reached with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (Finset.subset_union_left).trans (ih _)

def closureSearch (successors : State → Finset State) : Nat → Finset State → Finset State
  | 0, reached => reached
  | n + 1, reached =>
    let expanded := expand successors reached
    if expanded = reached then reached else closureSearch successors n expanded

theorem closureSearch_eq (successors : State → Finset State) (n : Nat)
    (reached : Finset State) :
    closureSearch successors n reached = expandRounds successors n reached := by
  induction n generalizing reached with
  | zero => rfl
  | succ n ih =>
    simp only [closureSearch]
    split
    next h => rw [expandRounds, h, expandRounds_fixed successors n reached h]
    next => exact ih _

variable [Fintype State]

def reachableSetFast (seeds : Finset State) (successors : State → Finset State) : Finset State :=
  closureSearch successors (Fintype.card State) seeds

@[simp] theorem reachableSetFast_eq (seeds : Finset State)
    (successors : State → Finset State) :
    reachableSetFast seeds successors = reachableSet seeds successors := by
  rw [reachableSetFast, closureSearch_eq, expandRounds_eq_layers, reachableSet]

/-- A Boolean query: success at discovery, failure only at stability or the bound. -/
def targetSearch (successors : State → Finset State) (target : State) :
    Nat → Finset State → Bool
  | 0, reached => decide (target ∈ reached)
  | n + 1, reached =>
    if target ∈ reached then true else
    let expanded := expand successors reached
    if expanded = reached then false else targetSearch successors target n expanded

omit [Fintype State] in
theorem targetSearch_eq (successors : State → Finset State) (target : State)
    (n : Nat) (reached : Finset State) :
    targetSearch successors target n reached = decide (target ∈ expandRounds successors n reached) := by
  induction n generalizing reached with
  | zero => rfl
  | succ n ih =>
    simp only [targetSearch]
    split
    next h => simp [subset_expandRounds successors (n + 1) reached h]
    next h =>
      split
      next heq => simp [expandRounds, heq, expandRounds_fixed successors n reached heq, h]
      next => exact ih _

def reachable? (seeds : Finset State) (successors : State → Finset State) (target : State) : Bool :=
  targetSearch successors target (Fintype.card State) seeds

@[simp] theorem reachable?_eq_true_iff (seeds : Finset State) (successors : State → Finset State)
    (target : State) : reachable? seeds successors target = true ↔ Reachable seeds successors target := by
  rw [reachable?, targetSearch_eq, expandRounds_eq_layers, decide_eq_true_eq]
  exact mem_reachableSet_iff

end KILT.Graph

namespace KILT.Graph
universe u
variable {State : Type u} [DecidableEq State]

/-- Forward route-table iteration, used only as a proof reference. -/
def routeRounds (order : Enumeration State) (successors : State → Finset State) :
    Nat → RouteTable State → RouteTable State
  | 0, previous => previous
  | n + 1, previous => routeRounds order successors n (expandRouteTable order successors previous)

theorem routeRounds_succ (order : Enumeration State) (successors : State → Finset State)
    (n : Nat) (previous : RouteTable State) :
    routeRounds order successors (n + 1) previous =
      expandRouteTable order successors (routeRounds order successors n previous) := by
  induction n generalizing previous with
  | zero => rfl
  | succ n ih => exact ih _

theorem routeRounds_initial (order : Enumeration State) (successors : State → Finset State)
    (n : Nat) (seeds : Finset State) :
    routeRounds order successors n (initialRouteTable seeds) = routeTables order seeds successors n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [routeRounds_succ, ih]; rfl

theorem routeRounds_fixed (order : Enumeration State) (successors : State → Finset State)
    (n : Nat) (previous : RouteTable State)
    (h : expandRouteTable order successors previous = previous) :
    routeRounds order successors n previous = previous := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [routeRounds, h] using ih

theorem routeRounds_retains (order : Enumeration State) (successors : State → Finset State)
    (n : Nat) (previous : RouteTable State) (target : State) (nodes : List State)
    (h : previous target = some nodes) :
    routeRounds order successors n previous target = some nodes := by
  induction n generalizing previous with
  | zero => exact h
  | succ n ih => exact ih _ (by simp [expandRouteTable, h])

/-- Scan stored results for a newly discovered state, without comparing routes. -/
def routeGrowth (previous : RouteTable State) (expanded : List (State × Option (List State))) : Bool :=
  expanded.any fun entry => (previous entry.1).isNone && entry.2.isSome

/-- No new discoveries implies the whole function-valued table is unchanged. -/
theorem routeGrowth_false (order : Enumeration State) (successors : State → Finset State)
    (previous : RouteTable State)
    (h : routeGrowth previous (materialize order (expandRouteTable order successors previous)) = false) :
    expandRouteTable order successors previous = previous := by
  simp only [routeGrowth, materialize, List.any_map, Function.comp_def, List.any_eq_false] at h
  funext s
  cases hp : previous s with
  | some nodes => simp [expandRouteTable, hp]
  | none =>
    have hs := h s (order.complete s)
    simpa [hp] using hs

/-- Materialized rounds with optional target discovery and no-new-state stopping.
A target query is intentionally not exposed as a complete route table. -/
def routeSearch (order : Enumeration State) (successors : State → Finset State)
    (target : Option State) : Nat → List (State × Option (List State)) →
      List (State × Option (List State))
  | 0, previous => previous
  | n + 1, previous =>
    if target.any (fun s => (tableLookup none previous s).isSome) then previous else
    let expanded := materialize order (expandRouteTable order successors (tableLookup none previous))
    if routeGrowth (tableLookup none previous) expanded then
      routeSearch order successors target n expanded else previous

/-- Full-table refinement, valid for arbitrary starting tables. -/
theorem routeSearch_none (order : Enumeration State) (successors : State → Finset State)
    (n : Nat) (previous : List (State × Option (List State))) :
    tableLookup none (routeSearch order successors none n previous) =
      routeRounds order successors n (tableLookup none previous) := by
  induction n generalizing previous with
  | zero => rfl
  | succ n ih =>
    simp only [routeSearch, Option.any_none, Bool.false_eq_true, ↓reduceIte]
    split
    next =>
      rw [ih]
      have heq : tableLookup none (materialize order
          (expandRouteTable order successors (tableLookup none previous))) =
          expandRouteTable order successors (tableLookup none previous) :=
        funext (tableLookup_materialize _ _ _)
      rw [heq]; rfl
    next h =>
      have hfix := routeGrowth_false order successors (tableLookup none previous) (by simpa using h)
      rw [routeRounds, hfix, routeRounds_fixed order successors n _ hfix]

/-- Target refinement preserves the exact first route, not just its existence. -/
theorem routeSearch_some (order : Enumeration State) (successors : State → Finset State)
    (target : State) (n : Nat) (previous : List (State × Option (List State))) :
    tableLookup none (routeSearch order successors (some target) n previous) target =
      routeRounds order successors n (tableLookup none previous) target := by
  induction n generalizing previous with
  | zero => rfl
  | succ n ih =>
    simp only [routeSearch, Option.any_some]
    split
    next h =>
      cases hp : tableLookup none previous target with
      | none => simp [hp] at h
      | some nodes => exact (routeRounds_retains order successors (n + 1) _ target nodes hp).symm
    next =>
      split
      next =>
        rw [ih]
        have heq : tableLookup none (materialize order
            (expandRouteTable order successors (tableLookup none previous))) =
            expandRouteTable order successors (tableLookup none previous) :=
          funext (tableLookup_materialize _ _ _)
        rw [heq]; rfl
      next h =>
        have hfix := routeGrowth_false order successors (tableLookup none previous) (by simpa using h)
        rw [routeRounds, hfix, routeRounds_fixed order successors n _ hfix]

variable [Fintype State]

def storedRoutesFast (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) : List (State × Option (List State)) :=
  routeSearch order successors none (Fintype.card State) (materialize order (initialRouteTable seeds))

@[simp] theorem storedRoutesFast_lookup (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (s : State) :
    tableLookup none (storedRoutesFast order seeds successors) s = route? order seeds successors s := by
  have h := congrFun (routeSearch_none order successors (Fintype.card State)
    (materialize order (initialRouteTable seeds))) s
  simpa only [storedRoutesFast, show tableLookup none (materialize order (initialRouteTable seeds)) =
    initialRouteTable seeds from funext (tableLookup_materialize _ _ _), routeRounds_initial, route?] using h

def routeFast? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (target : State) : Option (List State) :=
  tableLookup none (routeSearch order successors (some target) (Fintype.card State)
    (materialize order (initialRouteTable seeds))) target

@[simp] theorem routeFast?_eq (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (target : State) :
    routeFast? order seeds successors target = route? order seeds successors target := by
  have h := routeSearch_some order successors target (Fintype.card State)
    (materialize order (initialRouteTable seeds))
  simpa only [routeFast?, show tableLookup none (materialize order (initialRouteTable seeds)) =
    initialRouteTable seeds from funext (tableLookup_materialize _ _ _), routeRounds_initial, route?] using h

end KILT.Graph
