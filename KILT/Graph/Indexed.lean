import KILT.Graph.Enumeration
import KILT.Graph.Buchi
import Mathlib.Data.Finset.Sort
import Std.Data.ExtTreeMap.Lemmas

/-!
# Indexed finite graphs

Rows contain only dense vertex IDs. Bounds are carried by the vertex type, and
the outer array has exactly one row per vertex. The representation makes no
assumption that IDs agree with a user's witness-selection order.
-/
namespace KILT.Graph

/-- A finite graph with checked, sparse adjacency arrays. -/
structure IndexedGraph where
  size : Nat
  adjacency : Array (Array (Fin size))
  adjacency_size : adjacency.size = size

namespace IndexedGraph

abbrev Vertex (g : IndexedGraph) := Fin g.size

/-- Direct row lookup: no original-state equality or dictionary lookup. -/
def row (g : IndexedGraph) (i : g.Vertex) : Array g.Vertex :=
  g.adjacency[i.val]'(by simpa only [g.adjacency_size] using i.isLt)

/-- Finite-set view for the existing mathematical graph contracts. -/
def successors (g : IndexedGraph) (i : g.Vertex) : Finset g.Vertex :=
  (g.row i).toList.toFinset

@[simp] theorem mem_successors (g : IndexedGraph) (i j : g.Vertex) :
    j ∈ g.successors i ↔ j ∈ (g.row i).toList := by
  simp [successors]

/-- Executable adjacency test without constructing the finite-set proof view. -/
def edge (g : IndexedGraph) (i j : g.Vertex) : Bool := (g.row i).contains j

theorem edge_eq_decide (g : IndexedGraph) (i j : g.Vertex) :
    g.edge i j = decide (j ∈ g.successors i) := by
  apply Bool.eq_iff_iff.mpr
  simp [edge, successors]

end IndexedGraph

universe u
variable {State : Type u} [DecidableEq State]

namespace Enumeration

/-- Stable rank used for ties; this need not be a dense discovery ID. -/
def rank (order : Enumeration State) (s : State) : Fin order.states.length :=
  ⟨order.states.idxOf s, List.idxOf_lt_length_iff.mpr (order.complete s)⟩

@[simp] theorem get_rank (order : Enumeration State) (s : State) :
    order.states[(order.rank s).val] = s := by
  simp [rank]

theorem rank_injective (order : Enumeration State) : Function.Injective order.rank := by
  intro s t h
  have := congrArg (fun i : Fin order.states.length => order.states[i.val]) h
  simpa using this

/-- Enumerate a finite set by integer rank, without ordering its state type. -/
def ranked (order : Enumeration State) (states : Finset State) : List State :=
  ((states.map ⟨order.rank, order.rank_injective⟩).sort (· ≤ ·)).map
    (fun i => order.states[i.val])

@[simp] theorem mem_ranked (order : Enumeration State) (states : Finset State) (s : State) :
    s ∈ order.ranked states ↔ s ∈ states := by
  simp only [ranked, List.mem_map, Finset.mem_sort, Finset.mem_map]
  constructor
  · rintro ⟨i, ⟨t, ht, rfl⟩, heq⟩
    have heq' : t = s := by simpa using heq
    exact heq' ▸ ht
  · intro hs
    exact ⟨order.rank s, ⟨s, hs, rfl⟩, order.get_rank s⟩

theorem ranked_nodup (order : Enumeration State) (states : Finset State) :
    (order.ranked states).Nodup := by
  apply List.Nodup.map_on _ (Finset.sort_nodup _ _)
  intro i _ j _ h
  apply Fin.ext
  exact order.nodup.getElem_inj_iff.mp h

end Enumeration

namespace Enumeration

/-- Integer-keyed dictionary for dense IDs. A list prefix has earlier IDs. -/
def rankTableFrom (order : Enumeration State) : Nat → List State → Std.ExtTreeMap Nat Nat
  | _, [] => ∅
  | offset, s :: rest =>
    (rankTableFrom order (offset + 1) rest).insert (order.rank s).val offset

theorem rankTableFrom_lookup (order : Enumeration State) (offset : Nat)
    (states : List State) (s : State) :
    (order.rankTableFrom offset states)[(order.rank s).val]? =
      if s ∈ states then some (offset + states.idxOf s) else none := by
  induction states generalizing offset with
  | nil => simp [rankTableFrom]
  | cons t rest ih =>
    simp only [rankTableFrom, Std.ExtTreeMap.getElem?_insert]
    by_cases h : t = s
    · subst t
      simp
    · have hr : (order.rank t).val ≠ (order.rank s).val := by
        intro heq
        exact h (order.rank_injective (Fin.ext heq))
      simp only [compare_eq_iff_eq, hr, ↓reduceIte, ih]
      simp only [List.mem_cons, Ne.symm h, false_or, List.idxOf_cons, beq_iff_eq, h, ↓reduceIte]
      split <;> simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Enumeration

/-- Optional dense index, with bounds checked once at the representation boundary. -/
def denseIndex? (states : Array State) (s : State) : Option (Fin states.size) :=
  if h : states.toList.idxOf s < states.size then some ⟨states.toList.idxOf s, h⟩ else none

theorem denseIndex?_eq_some_iff (states : Array State) (hn : states.toList.Nodup)
    (s : State) (i : Fin states.size) :
    denseIndex? states s = some i ↔ states[i.val] = s := by
  simp only [denseIndex?]
  split
  next h =>
    constructor
    · intro hi
      have heq := Option.some.inj hi
      subst i
      exact List.getElem_idxOf (xs := states.toList) h
    · intro hi
      apply congrArg some
      apply Fin.ext
      have hi' : states.toList[i.val] = s := hi
      have hx : states.toList[states.toList.idxOf s] = s := List.getElem_idxOf h
      exact hn.getElem_inj_iff.mp (hx.trans hi'.symm)
  next h =>
    constructor
    · intro heq; cases heq
    · intro hi
      have hm : s ∈ states.toList := hi ▸ Array.getElem_mem_toList i.isLt
      exact (h (by simpa only [Array.length_toList] using List.idxOf_lt_length_iff.mpr hm)).elim

/-- Lookup integer ranks in a supplied sparse dictionary, checking its boundary. -/
def rankIndex? (order : Enumeration State) (states : Array State)
    (table : Std.ExtTreeMap Nat Nat) (s : State) : Option (Fin states.size) :=
  (table[(order.rank s).val]?).bind fun i =>
    if h : i < states.size then some ⟨i, h⟩ else none

theorem rankIndex?_eq_denseIndex? (order : Enumeration State) (states : Array State) (s : State) :
    rankIndex? order states (order.rankTableFrom 0 states.toList) s = denseIndex? states s := by
  simp only [rankIndex?, Enumeration.rankTableFrom_lookup, Nat.zero_add]
  by_cases h : s ∈ states.toList
  · simp only [h, ↓reduceIte, Option.bind_some]
    rfl
  · simp only [h, ↓reduceIte, Option.bind_none]
    symm
    simp only [denseIndex?]
    have hn : ¬states.toList.idxOf s < states.size := by
      simpa only [← Array.length_toList, List.idxOf_lt_length_iff] using h
    simp [hn]

/-- Reachability-restricted storage. Coverage and edge equations are proofs;
queries consume only the indexed graph, decoder and seed IDs. -/
structure PreparedReachable [Fintype State] (seeds : Finset State)
    (next : State → Finset State) where
  graph : IndexedGraph
  states : Array State
  states_size : states.size = graph.size
  nodup : states.toList.Nodup
  initials : Finset graph.Vertex
  coverage : ∀ s, s ∈ states.toList ↔ Reachable seeds next s
  initial_iff : ∀ i : graph.Vertex,
    i ∈ initials ↔ states[i.val]'(by simpa only [states_size] using i.isLt) ∈ seeds
  edge_iff : ∀ i j : graph.Vertex,
    j ∈ graph.successors i ↔
      states[j.val]'(by simpa only [states_size] using j.isLt) ∈
        next (states[i.val]'(by simpa only [states_size] using i.isLt))
  sourceOrder : Enumeration State
  ranks : Array Nat
  ranks_size : ranks.size = graph.size
  ranks_correct : ∀ i : graph.Vertex,
    ranks[i.val]'(by simpa only [ranks_size] using i.isLt) =
      (sourceOrder.rank (states[i.val]'(by simpa only [states_size] using i.isLt))).val

end KILT.Graph
