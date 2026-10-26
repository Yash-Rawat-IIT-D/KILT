import KILT.Graph.Basic

/-!
# Reachable-only work queue

A pending state has no completed row. A processed deadlock has a completed row
whose successor set is empty. These cases must remain distinct.
-/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

namespace ReachableQueue

/-- Each row is computed once, when its source leaves the pending queue. -/
structure Work (State : Type u) where
  rows : List (State × Finset State)
  pending : List State

def Work.nodes (w : Work State) : List State := w.rows.map Prod.fst ++ w.pending

open Work

structure Invariant (seeds : Finset State) (next : State → Finset State)
    (w : Work State) : Prop where
  nodup : w.nodes.Nodup
  seeds_mem : ∀ s ∈ seeds, s ∈ w.nodes
  sound : ∀ s ∈ w.nodes, Reachable seeds next s
  rows : ∀ row ∈ w.rows, row.2 = next row.1
  covered : ∀ row ∈ w.rows, ∀ s ∈ row.2, s ∈ w.nodes

def initial (order : Enumeration State) (seeds : Finset State) : Work State :=
  ⟨[], order.ranked seeds⟩

theorem initial_invariant (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : Invariant seeds next (initial order seeds) := by
  refine ⟨order.ranked_nodup seeds, ?_, ?_, ?_, ?_⟩
  · simpa [initial, nodes] using (fun s hs => (order.mem_ranked seeds s).mpr hs)
  · intro s hs
    have hs' : s ∈ seeds := by simpa [initial, nodes] using hs
    exact ⟨s, hs', .refl⟩
  · simp [initial]
  · simp [initial]

/-- Processing preserves discovery order: completed sources followed by the
pending queue are the original nodes followed by the newly discovered nodes. -/
def advance (order : Enumeration State) (next : State → Finset State)
    (w : Work State) : Work State :=
  match w.pending with
  | [] => w
  | s :: rest =>
    let edges := next s
    let fresh := order.ranked (edges \ w.nodes.toFinset)
    ⟨w.rows ++ [(s, edges)], rest ++ fresh⟩

theorem nodes_advance (order : Enumeration State) (next : State → Finset State)
    (w : Work State) (s : State) (rest : List State) (hp : w.pending = s :: rest) :
    (advance order next w).nodes =
      w.nodes ++ order.ranked (next s \ w.nodes.toFinset) := by
  simp [advance, hp, nodes, List.append_assoc]

theorem advance_invariant (order : Enumeration State) (next : State → Finset State)
    (seeds : Finset State) (w : Work State) (h : Invariant seeds next w) :
    Invariant seeds next (advance order next w) := by
  cases hp : w.pending with
  | nil => simpa [advance, hp] using h
  | cons s rest =>
    have hn := nodes_advance order next w s rest hp
    have hs : s ∈ w.nodes := by simp [nodes, hp]
    have hold : ∀ t ∈ w.nodes, t ∈ (advance order next w).nodes := by
      intro t ht
      rw [hn]
      exact List.mem_append_left _ ht
    refine ⟨?_, fun t ht => hold t (h.seeds_mem t ht), ?_, ?_, ?_⟩
    · rw [hn, List.nodup_append]
      refine ⟨h.nodup, order.ranked_nodup _, ?_⟩
      intro t ht u hu heq
      have hu' := (order.mem_ranked _ u).mp hu
      have hnot := (Finset.mem_sdiff.mp hu').2
      exact hnot (by simpa [heq] using ht)
    · intro t ht
      rw [hn] at ht
      rcases List.mem_append.mp ht with ht | ht
      · exact h.sound t ht
      · obtain ⟨start, hstart, path⟩ := h.sound s hs
        have hedge := (Finset.mem_sdiff.mp ((order.mem_ranked _ t).mp ht)).1
        exact ⟨start, hstart, path.tail hedge⟩
    · intro row hr
      simp only [advance, hp] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h.rows row hr
      · simpa using (List.mem_singleton.mp hr ▸ rfl : row.2 = next row.1)
    · intro row hr t ht
      simp only [advance, hp] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hold t (h.covered row hr t ht)
      · have heq := List.mem_singleton.mp hr
        subst row
        by_cases hm : t ∈ w.nodes
        · exact hold t hm
        · rw [hn]
          exact List.mem_append_right _ ((order.mem_ranked _ t).mpr
            (Finset.mem_sdiff.mpr ⟨ht, by simpa using hm⟩))

def run (order : Enumeration State) (next : State → Finset State) : Nat → Work State → Work State
  | 0, w => w
  | fuel + 1, w =>
    if w.pending.isEmpty then w else run order next fuel (advance order next w)

theorem run_invariant (order : Enumeration State) (next : State → Finset State)
    (seeds : Finset State) (fuel : Nat) (w : Work State) (h : Invariant seeds next w) :
    Invariant seeds next (run order next fuel w) := by
  induction fuel generalizing w with
  | zero => exact h
  | succ fuel ih =>
    simp only [run]
    split
    · exact h
    · exact ih _ (advance_invariant order next seeds w h)

/-- An unfinished queue processes one distinct source per unit of fuel. -/
theorem run_progress (order : Enumeration State) (next : State → Finset State)
    (fuel : Nat) (w : Work State) :
    (run order next fuel w).pending = [] ∨
      w.rows.length + fuel ≤ (run order next fuel w).rows.length := by
  induction fuel generalizing w with
  | zero => exact Or.inr (Nat.le_refl _)
  | succ fuel ih =>
    cases hp : w.pending with
    | nil => exact Or.inl (by simp [run, hp])
    | cons s rest =>
      have heq : run order next (fuel + 1) w = run order next fuel (advance order next w) := by
        simp [run, hp]
      rw [heq]
      rcases ih (advance order next w) with h | h
      · exact Or.inl h
      · right
        have hl : (advance order next w).rows.length = w.rows.length + 1 := by
          simp [advance, hp]
        omega

def prepare (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : Work State :=
  run order next (Fintype.card State) (initial order seeds)

theorem prepare_invariant (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : Invariant seeds next (prepare order seeds next) :=
  run_invariant _ _ _ _ _ (initial_invariant _ _ _)

theorem prepare_complete (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : (prepare order seeds next).pending = [] := by
  have hi := prepare_invariant order seeds next
  have bound := List.Nodup.length_le_card hi.nodup
  rcases run_progress order next (Fintype.card State) (initial order seeds) with h | h
  · exact h
  · change (initial order seeds).rows.length + Fintype.card State ≤
        (prepare order seeds next).rows.length at h
    simp only [initial, List.length_nil, Nat.zero_add] at h
    have length : (prepare order seeds next).nodes.length =
        (prepare order seeds next).rows.length + (prepare order seeds next).pending.length := by
      simp [nodes]
    have : (prepare order seeds next).pending.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this

theorem prepare_mem_iff (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (s : State) :
    s ∈ (prepare order seeds next).nodes ↔ Reachable seeds next s := by
  have hi := prepare_invariant order seeds next
  constructor
  · exact hi.sound s
  · rintro ⟨start, hstart, path⟩
    induction path with
    | refl => exact hi.seeds_mem start hstart
    | @tail t u path edge ih =>
      have ht : t ∈ (prepare order seeds next).rows.map Prod.fst := by
        simpa [nodes, prepare_complete] using ih
      obtain ⟨row, hr, heq⟩ := List.mem_map.mp ht
      exact hi.covered row hr u (by simpa [hi.rows row hr, heq, Step] using edge)

end ReachableQueue


namespace ReachableQueue

structure Buffer (State : Type u) where
  nodes : Array State
  cursor : Nat
  rows : Array (State × Finset State)
  seen : Finset State

namespace Buffer

def view (b : Buffer State) : Work State := ⟨b.rows.toList, b.nodes.toList.drop b.cursor⟩

def Valid (b : Buffer State) : Prop :=
  b.cursor ≤ b.nodes.size ∧ b.cursor = b.rows.size ∧
  b.rows.toList.map Prod.fst = b.nodes.toList.take b.cursor ∧
  b.seen = b.nodes.toList.toFinset

def initial (order : Enumeration State) (seeds : Finset State) : Buffer State :=
  ⟨(order.ranked seeds).toArray, 0, #[], seeds⟩

theorem initial_valid (order : Enumeration State) (seeds : Finset State) :
    Valid (initial order seeds) := by
  unfold Valid initial
  simp only [List.size_toArray, Array.size_empty, Nat.zero_le, List.toList_toArray,
    Array.toList_empty, List.map_nil, List.take_zero, true_and]
  constructor
  · rfl
  · ext s
    simp

theorem initial_view (order : Enumeration State) (seeds : Finset State) :
    (initial order seeds).view = ReachableQueue.initial order seeds := by
  simp [view, initial, ReachableQueue.initial]

theorem view_nodes (b : Buffer State) (h : b.Valid) : b.view.nodes = b.nodes.toList := by
  simp only [view, Work.nodes]
  rw [h.2.2.1, List.take_append_drop]

def advance (order : Enumeration State) (next : State → Finset State)
    (b : Buffer State) : Buffer State :=
  if h : b.cursor < b.nodes.size then
    let source := b.nodes[b.cursor]
    let edges := next source
    let fresh := order.ranked (edges \ b.seen)
    ⟨b.nodes ++ fresh.toArray, b.cursor + 1, b.rows.push (source, edges),
      b.seen ∪ fresh.toFinset⟩
  else b

theorem advance_view (order : Enumeration State) (next : State → Finset State)
    (b : Buffer State) (v : b.Valid) :
    (b.advance order next).view = ReachableQueue.advance order next b.view := by
  unfold advance
  split
  next h =>
    have hl : b.cursor < b.nodes.toList.length := by simpa using h
    have hd := List.drop_eq_getElem_cons hl
    have hf : b.view.nodes.toFinset = b.seen := by rw [view_nodes b v, ← v.2.2.2]
    have hf' : (Work.mk b.rows.toList
        (b.nodes.toList[b.cursor] :: b.nodes.toList.drop (b.cursor + 1))).nodes.toFinset = b.seen := by
      simpa [view, hd] using hf
    simp only [view, ReachableQueue.advance, hd, hf', Array.getElem_toList]
    simp only [Array.toList_push, Array.toList_append, List.toList_toArray]
    rw [List.drop_append_of_le_length (by simpa using Nat.succ_le_of_lt h)]
    simp only [Array.getElem_toList] at hf'
    rw [hf']
  next h =>
    have he : b.nodes.toList.drop b.cursor = [] := by
      apply List.drop_eq_nil_of_le
      simpa using Nat.le_of_not_gt h
    simp [view, ReachableQueue.advance, he]

theorem advance_valid (order : Enumeration State) (next : State → Finset State)
    (b : Buffer State) (v : b.Valid) : (b.advance order next).Valid := by
  unfold advance
  split
  next h =>
    have hl : b.cursor < b.nodes.toList.length := by simpa using h
    rcases v with ⟨hbound, hcursor, hrows, hseen⟩
    simp only [Valid, Array.size_append, List.size_toArray, Array.size_push,
      Array.toList_push, Array.toList_append, List.toList_toArray, List.map_append,
      List.map_cons, List.map_nil, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [List.take_append_of_le_length (by simpa using Nat.succ_le_of_lt h)]
      rw [List.take_succ_eq_append_getElem hl]
      simp [hrows]
    · rw [hseen]
  next h => exact v

def run (order : Enumeration State) (next : State → Finset State) : Nat → Buffer State → Buffer State
  | 0, b => b
  | fuel + 1, b => if b.cursor < b.nodes.size then run order next fuel (b.advance order next) else b

theorem run_view (order : Enumeration State) (next : State → Finset State)
    (fuel : Nat) (b : Buffer State) (v : b.Valid) :
    (b.run order next fuel).view = ReachableQueue.run order next fuel b.view := by
  induction fuel generalizing b with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, ReachableQueue.run]
    by_cases h : b.cursor < b.nodes.size
    · have hl : b.cursor < b.nodes.toList.length := by simpa using h
      have hn : b.view.pending.isEmpty = false := by simp [view, List.drop_eq_getElem_cons hl]
      simp only [h, ↓reduceIte, hn, Bool.false_eq_true]
      rw [ih _ (advance_valid order next b v), advance_view order next b v]
    · have he : b.nodes.toList.drop b.cursor = [] := by
        apply List.drop_eq_nil_of_le
        simpa using Nat.le_of_not_gt h
      simp [h, view, he]

def prepare (order : Enumeration State) (seeds : Finset State) (next : State → Finset State) : Buffer State :=
  (initial order seeds).run order next (Fintype.card State)

theorem prepare_view (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : (prepare order seeds next).view = ReachableQueue.prepare order seeds next := by
  unfold prepare ReachableQueue.prepare
  rw [run_view _ _ _ _ (initial_valid _ _), initial_view]

end Buffer
end ReachableQueue

/-- Convert one cached successor set; original successors are not recomputed. -/
def adjacencyRow (order : Enumeration State) (states : Array State)
    (edges : Finset State) : Array (Fin states.size) :=
  ((order.ranked edges).filterMap (denseIndex? states)).toArray

theorem mem_adjacencyRow (order : Enumeration State) (states : Array State)
    (hn : states.toList.Nodup) (edges : Finset State) (i : Fin states.size) :
    i ∈ (adjacencyRow order states edges).toList ↔ states[i.val] ∈ edges := by
  simp only [adjacencyRow, List.toList_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, hi⟩
    have heq := (denseIndex?_eq_some_iff states hn s i).mp hi
    exact heq ▸ ((order.mem_ranked edges s).mp hs)
  · intro hi
    exact ⟨states[i.val], (order.mem_ranked edges _).mpr hi,
      (denseIndex?_eq_some_iff states hn _ i).mpr rfl⟩

/-- Construct dense adjacency from a completed, verified work queue. -/
private def prepareFromWork (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) (w : ReachableQueue.Work State)
    (hw : ReachableQueue.Invariant seeds next w) (hp : w.pending = [])
    (hc : ∀ s, s ∈ w.nodes ↔ Reachable seeds next s) : PreparedReachable seeds next := by
  let states := (w.rows.map Prod.fst).toArray
  have hn : states.toList.Nodup := by
    simpa [states, ReachableQueue.Work.nodes, hp] using hw.nodup
  let ids := order.rankTableFrom 0 states.toList
  let adjacency := (w.rows.map (fun row =>
    ((order.ranked row.2).filterMap (rankIndex? order states ids)).toArray)).toArray
  let graph : FiniteGraph := ⟨states.size, adjacency, by simp [adjacency, states]⟩
  refine ⟨graph, states, rfl, hn,
    Finset.univ.filter (fun i => states[i.val] ∈ seeds), ?_, ?_, ?_⟩
  · intro s
    simpa [states, ReachableQueue.Work.nodes, hp] using hc s
  · intro i
    simp
  · intro i j
    change j ∈ ((adjacency[i.val]'_).toList.toFinset) ↔ states[j.val] ∈ next states[i.val]
    rw [List.mem_toFinset]
    have hi : i.val < w.rows.length := by simpa [graph, states] using i.isLt
    have hrow : w.rows[i.val].2 = next w.rows[i.val].1 :=
      hw.rows _ (List.getElem_mem hi)
    simp only [adjacency, List.getElem_toArray, List.getElem_map]
    have lookup : rankIndex? order states ids = denseIndex? states :=
      funext (rankIndex?_eq_denseIndex? order states)
    have hm := mem_adjacencyRow order states hn w.rows[i.val].2 j
    have hstate : states[i.val] = w.rows[i.val].1 := by
      simp only [states, List.getElem_toArray, List.getElem_map]
    simpa only [adjacencyRow, List.toList_toArray, lookup, hrow, hstate] using hm

/-- Mathematical list-queue reference, used only for refinement proofs. -/
def Specification.prepareReachable (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : PreparedReachable seeds next :=
  prepareFromWork order seeds next (ReachableQueue.prepare order seeds next)
    (ReachableQueue.prepare_invariant order seeds next)
    (ReachableQueue.prepare_complete order seeds next)
    (ReachableQueue.prepare_mem_iff order seeds next)

/-- Reachable preparation using the verified incremental buffer. -/
def prepareReachable (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) : PreparedReachable seeds next := by
  let w := (ReachableQueue.Buffer.prepare order seeds next).view
  have hv : w = ReachableQueue.prepare order seeds next := ReachableQueue.Buffer.prepare_view order seeds next
  have hw : ReachableQueue.Invariant seeds next w := by rw [hv]; exact ReachableQueue.prepare_invariant order seeds next
  have hp : w.pending = [] := by rw [hv]; exact ReachableQueue.prepare_complete order seeds next
  have hc : ∀ s, s ∈ w.nodes ↔ Reachable seeds next s := by
    rw [hv]
    exact ReachableQueue.prepare_mem_iff order seeds next
  exact prepareFromWork order seeds next w hw hp hc

theorem prepareReachable_eq_reference (order : Enumeration State) (seeds : Finset State)
    (next : State → Finset State) :
    prepareReachable order seeds next = Specification.prepareReachable order seeds next := by
  simp only [prepareReachable, Specification.prepareReachable, ReachableQueue.Buffer.prepare_view]

end KILT.Graph
