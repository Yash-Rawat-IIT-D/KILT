import KILT.Graph.Routes

/-!
# Materialized route rounds

Each round stores values, rather than a tower of lookup functions. Lookup is
linear in the explicit enumeration. The table theorem below preserves the
existing route algorithm, including its deterministic predecessor choices.
-/
namespace KILT.Graph
universe u v
variable {State : Type u} {Value : Type v} [DecidableEq State]

/-- Ordered association table; missing keys use an explicit default. -/
def tableLookup (fallback : Value) : List (State × Value) → State → Value
  | [], _ => fallback
  | (key, value) :: rest, target =>
      if key = target then value else tableLookup fallback rest target

def materialize (order : Enumeration State) (f : State → Value) : List (State × Value) :=
  order.states.map fun s => (s, f s)

private theorem tableLookup_map (fallback : Value) (states : List State)
    (f : State → Value) (s : State) (hs : s ∈ states) :
    tableLookup fallback (states.map fun t => (t, f t)) s = f s := by
  induction states with
  | nil => simp at hs
  | cons a rest ih =>
    simp only [List.map_cons, tableLookup]
    split
    next h => simp [h]
    next h =>
      apply ih
      rcases List.mem_cons.mp hs with heq | hrest
      · exact (h heq.symm).elim
      · exact hrest

@[simp] theorem tableLookup_materialize (fallback : Value) (order : Enumeration State)
    (f : State → Value) (s : State) :
    tableLookup fallback (materialize order f) s = f s :=
  tableLookup_map fallback order.states f s (order.complete s)

variable [Fintype State]

def storedRouteTables (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) : Nat → List (State × Option (List State))
  | 0 => materialize order (initialRouteTable seeds)
  | n + 1 =>
      let previous := storedRouteTables order seeds successors n
      materialize order (expandRouteTable order successors (tableLookup none previous))

omit [Fintype State] in
/-- Materialization changes evaluation, not routes or selection order. -/
@[simp] theorem storedRouteTables_lookup (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (n : Nat) (s : State) :
    tableLookup none (storedRouteTables order seeds successors n) s =
      routeTables order seeds successors n s := by
  induction n generalizing s with
  | zero => simp [storedRouteTables, routeTables]
  | succ n ih =>
      have heq : tableLookup none (storedRouteTables order seeds successors n) =
          routeTables order seeds successors n := funext ih
      simp [storedRouteTables, routeTables, heq]

def storedRoutes (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) : List (State × Option (List State)) :=
  storedRouteTables order seeds successors (Fintype.card State)

@[simp] theorem storedRoutes_lookup (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (s : State) :
    tableLookup none (storedRoutes order seeds successors) s = route? order seeds successors s :=
  storedRouteTables_lookup order seeds successors _ s

end KILT.Graph
