import KILT.Graph.Correspondence
import KILT.Graph.Specification.Rounds

/-! Boolean visited arrays and new-discovery frontiers. -/
namespace KILT.Graph.FiniteGraph

structure Visits (g : FiniteGraph) where
  bits : Array Bool
  size_eq : bits.size = g.size
  frontier : List g.Vertex

def Visits.get {g : FiniteGraph} (v : Visits g) (i : g.Vertex) : Bool :=
  v.bits[i.val]'(by simpa only [v.size_eq] using i.isLt)

def Visits.view {g : FiniteGraph} (v : Visits g) : Finset g.Vertex :=
  Finset.univ.filter (fun i => v.get i)

@[simp] theorem Visits.mem_view {g : FiniteGraph} (v : Visits g) (i : g.Vertex) :
    i ∈ v.view ↔ v.get i = true := by simp [view]

structure Visits.Valid {g : FiniteGraph} (v : Visits g) : Prop where
  covered : ∀ i ∈ v.frontier, v.get i = true
  past : ∀ i, v.get i = true → i ∉ v.frontier → ∀ j ∈ g.successors i, v.get j = true

def Visits.initial (g : FiniteGraph) (seeds : Finset g.Vertex) : Visits g :=
  ⟨Array.ofFn (fun i => decide (i ∈ seeds)), by simp,
    (List.finRange g.size).filter (fun i => decide (i ∈ seeds))⟩

theorem Visits.initial_valid (g : FiniteGraph) (seeds : Finset g.Vertex) :
    (Visits.initial g seeds).Valid := by
  constructor
  · intro i hi
    simpa [initial, get] using (List.mem_filter.mp hi).2
  · intro i hi hnot
    have hm : i ∈ seeds := by simpa [initial, get] using hi
    exact (hnot (by simp [initial, hm])).elim

@[simp] theorem Visits.initial_view (g : FiniteGraph) (seeds : Finset g.Vertex) :
    (Visits.initial g seeds).view = seeds := by
  ext i
  simp [initial, get]

def Visits.advance {g : FiniteGraph} (v : Visits g) : Visits g :=
  let bits := Array.ofFn (fun target => v.get target || v.frontier.any
    (fun source => g.edge source target))
  ⟨bits, by simp [bits], (List.finRange g.size).filter
    (fun i => !v.get i && bits[i.val]'(by simpa [bits] using i.isLt))⟩

theorem Visits.get_advance {g : FiniteGraph} (v : Visits g) (i : g.Vertex) :
    v.advance.get i = (v.get i || v.frontier.any (fun source => decide (i ∈ g.successors source))) := by
  simp [advance, get, edge_eq_decide]

theorem Visits.mem_advance_frontier {g : FiniteGraph} (v : Visits g) (i : g.Vertex) :
    i ∈ v.advance.frontier ↔ v.get i = false ∧ v.advance.get i = true := by
  simp [advance, get, edge_eq_decide]

theorem Visits.advance_valid {g : FiniteGraph} (v : Visits g) (h : v.Valid) : v.advance.Valid := by
  constructor
  · intro i hi
    exact ((v.mem_advance_frontier i).mp hi).2
  · intro i hi hnot j hj
    have hold : v.get i = true := by
      cases he : v.get i with
      | true => rfl
      | false => exact (hnot ((v.mem_advance_frontier i).mpr ⟨he, hi⟩)).elim
    rw [get_advance, Bool.or_eq_true_iff]
    by_cases hf : i ∈ v.frontier
    · right
      exact List.any_eq_true.mpr ⟨i, hf, by simpa using hj⟩
    · exact Or.inl (h.past i hold hf j hj)

theorem Visits.advance_view {g : FiniteGraph} (v : Visits g) (h : v.Valid) :
    v.advance.view = expand g.successors v.view := by
  ext target
  simp only [mem_view, get_advance, Bool.or_eq_true_iff, List.any_eq_true, decide_eq_true_eq,
    expand, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (hold | ⟨source, hs, he⟩)
    · exact Or.inl hold
    · exact Or.inr ⟨source, h.covered source hs, he⟩
  · rintro (hold | ⟨source, hs, he⟩)
    · exact Or.inl hold
    · by_cases hf : source ∈ v.frontier
      · exact Or.inr ⟨source, hf, he⟩
      · exact Or.inl (h.past source hs hf target he)

theorem Visits.empty_fixed {g : FiniteGraph} (v : Visits g) (h : v.Valid)
    (he : v.frontier = []) : expand g.successors v.view = v.view := by
  rw [← v.advance_view h]
  ext i
  simp [get_advance, he]

def Visits.search {g : FiniteGraph} (target : g.Vertex) : Nat → Visits g → Bool
  | 0, v => v.get target
  | fuel + 1, v =>
    if v.get target then true else
      if v.frontier.isEmpty then false else Visits.search target fuel v.advance

theorem Visits.search_eq {g : FiniteGraph} (target : g.Vertex) (fuel : Nat)
    (v : Visits g) (h : v.Valid) :
    v.search target fuel = decide (target ∈ expandRounds g.successors fuel v.view) := by
  induction fuel generalizing v with
  | zero => simp [search, expandRounds]
  | succ fuel ih =>
    simp only [search]
    split
    next found =>
      have hm : target ∈ v.view := (v.mem_view target).mpr found
      exact (decide_eq_true ((subset_expandRounds _ (fuel + 1) _ hm))).symm
    next absent =>
      split
      next empty =>
        have he : v.frontier = [] := List.isEmpty_iff.mp empty
        have hf := v.empty_fixed h he
        simp only [expandRounds, hf, expandRounds_fixed _ fuel _ hf]
        simp_all
      next =>
        rw [ih _ (v.advance_valid h), v.advance_view h]
        rfl

/-- Boolean reachability with no parent or complete-route allocation. -/
def reachable? (g : FiniteGraph) (seeds : Finset g.Vertex) (target : g.Vertex) : Bool :=
  (Visits.initial g seeds).search target g.size

theorem reachable?_eq_spec (g : FiniteGraph) (seeds : Finset g.Vertex) (target : g.Vertex) :
    g.reachable? seeds target = decide (target ∈ reachableSetSpec seeds g.successors) := by
  rw [reachable?, Visits.search_eq _ _ _ (Visits.initial_valid g seeds), Visits.initial_view,
    expandRounds_eq_layers]
  simp only [reachableSetSpec, Fintype.card_fin]

/-- Positive return query, skipping array allocation for deadlocks and self-loops. -/
def canReturn? (g : FiniteGraph) (q : g.Vertex) : Bool :=
  if (g.row q).size = 0 then false else
    if g.edge q q then true else g.reachable? (g.successors q) q

theorem canReturn?_eq_reachable (g : FiniteGraph) (q : g.Vertex) :
    canReturn? g q = g.reachable? (g.successors q) q := by
  unfold canReturn?
  split
  next he =>
    have hs : g.successors q = ∅ := by
      simp [successors, Array.eq_empty_of_size_eq_zero he]
    rw [hs, reachable?_eq_spec]
    simp
  next =>
    split
    next he =>
      have hq : q ∈ g.successors q := by simpa [edge_eq_decide] using he
      rw [reachable?_eq_spec]
      symm
      apply decide_eq_true
      exact mem_reachableSetSpec_iff.mpr ⟨q, hq, .refl⟩
    next => rfl

end KILT.Graph.FiniteGraph
