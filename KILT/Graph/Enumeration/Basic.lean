import Mathlib.Data.List.Nodup

/-! Complete, duplicate-free orders, independent of graph algorithms. -/
namespace KILT.Graph
universe u

/-- An explicit traversal order for deterministic witness selection. -/
structure Enumeration (State : Type u) where
  states : List State
  nodup : states.Nodup
  complete : ∀ state, state ∈ states

end KILT.Graph
