import KILT.Graph.Specification.Routes

/-! Finite expansion recurrences used as proof specifications, not search backends. -/
namespace KILT.Graph
universe u
variable {State : Type u} [DecidableEq State]

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


end KILT.Graph
