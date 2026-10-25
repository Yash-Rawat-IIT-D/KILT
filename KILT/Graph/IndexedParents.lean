import KILT.Graph.IndexedCorrect

/-!
# Parent storage and reconstruction

Entries contain only a root marker or a predecessor ID and depth. The
representation predicate is proof-only: complete routes are not stored in the
executable forest. Reconstruction follows predecessor IDs with an accumulator.
-/
namespace KILT.Graph.IndexedGraph

inductive Parent (n : Nat) where
  | unseen
  | root
  | via (source : Fin n) (depth : Nat)
  deriving DecidableEq, Repr

def Parent.depth : Parent n → Option Nat
  | .unseen => none
  | .root => some 0
  | .via _ d => some d

structure Parents (g : IndexedGraph) where
  entries : Array (Parent g.size)
  size_eq : entries.size = g.size

def Parents.get {g : IndexedGraph} (p : Parents g) (i : g.Vertex) : Parent g.size :=
  p.entries[i.val]'(by simpa only [p.size_eq] using i.isLt)

/-- A proof-only relationship to a route specification. -/
def Parents.Represents {g : IndexedGraph} (p : Parents g) (routes : RouteTable g.Vertex) : Prop :=
  ∀ i, match p.get i with
  | .unseen => routes i = none
  | .root => routes i = some [i]
  | .via source depth => ∃ path, routes source = some path ∧
      routes i = some (path ++ [i]) ∧ path.length = depth

theorem Parents.represents_nonempty {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes) (i : g.Vertex)
    {path : List g.Vertex} (hp : routes i = some path) : path ≠ [] := by
  have hi := h i
  cases he : p.get i with
  | unseen => simp [he, hp] at hi
  | root =>
    simp only [he] at hi
    have := Option.some.inj (hp.symm.trans hi)
    simp [this]
  | via source depth =>
    simp only [he] at hi
    obtain ⟨prior, _, hr, _⟩ := hi
    have := Option.some.inj (hp.symm.trans hr)
    simp [this]

theorem Parents.represents_depth {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes) (i : g.Vertex)
    {path : List g.Vertex} (hp : routes i = some path) :
    (p.get i).depth = some (path.length - 1) := by
  have hi := h i
  cases he : p.get i with
  | unseen => simp [he, hp] at hi
  | root =>
    simp only [he] at hi
    have hx := Option.some.inj (hp.symm.trans hi)
    simp [Parent.depth, hx]
  | via source depth =>
    simp only [he] at hi
    obtain ⟨prior, _, hr, hd⟩ := hi
    have hx := Option.some.inj (hp.symm.trans hr)
    simp [Parent.depth, hx, hd]

def Parents.unwind {g : IndexedGraph} (p : Parents g) :
    Nat → g.Vertex → List g.Vertex → Option (List g.Vertex)
  | 0, _, _ => none
  | fuel + 1, target, suffix =>
    match p.get target with
    | .unseen => none
    | .root => some (target :: suffix)
    | .via source _ => p.unwind fuel source (target :: suffix)

/-- Following pointers reconstructs the specification route. The complete route
appears only in the theorem and the successful output, not in parent entries. -/
theorem Parents.unwind_correct {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes)
    (fuel : Nat) (target : g.Vertex) (suffix : List g.Vertex)
    (path : List g.Vertex) (hp : routes target = some path) (bound : path.length ≤ fuel) :
    p.unwind fuel target suffix = some (path ++ suffix) := by
  induction fuel generalizing target suffix path with
  | zero =>
    have hn := p.represents_nonempty h target hp
    have : path = [] := List.length_eq_zero_iff.mp (by omega)
    exact (hn this).elim
  | succ fuel ih =>
    have ht := h target
    cases he : p.get target with
    | unseen => simp [he, hp] at ht
    | root =>
      simp only [he] at ht
      have hx := Option.some.inj (hp.symm.trans ht)
      simp [unwind, he, hx]
    | via source depth =>
      simp only [he] at ht
      obtain ⟨prior, hprior, hpath, _⟩ := ht
      have hx := Option.some.inj (hp.symm.trans hpath)
      have hb : prior.length ≤ fuel := by
        simp only [hx, List.length_append, List.length_singleton] at bound
        omega
      simpa [unwind, he, hx, List.append_assoc] using
        ih source (target :: suffix) prior hprior hb

/-- Any represented parent points to a strictly smaller discovery depth. -/
theorem Parents.parent_depth_lt {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes)
    (target source : g.Vertex) (depth : Nat) (he : p.get target = .via source depth) :
    ∃ sourceDepth, (p.get source).depth = some sourceDepth ∧ sourceDepth < depth := by
  have ht := h target
  simp only [he] at ht
  obtain ⟨prior, hp, _, hd⟩ := ht
  refine ⟨prior.length - 1, p.represents_depth h source hp, ?_⟩
  have hn := p.represents_nonempty h source hp
  have hl := List.length_pos_iff.mpr hn
  omega

def Parents.initial (g : IndexedGraph) (seeds : Finset g.Vertex) : Parents g :=
  ⟨Array.ofFn (fun i => if i ∈ seeds then .root else .unseen), by simp⟩

theorem Parents.initial_represents (g : IndexedGraph) (seeds : Finset g.Vertex) :
    (Parents.initial g seeds).Represents (initialRouteTable seeds) := by
  intro i
  simp only [initial, get, Array.getElem_ofFn]
  by_cases hi : i ∈ seeds <;> simp [hi, initialRouteTable]

theorem Parents.isSome_iff {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes) (i : g.Vertex) :
    (p.get i).depth.isSome = (routes i).isSome := by
  have hi := h i
  cases he : p.get i with
  | unseen => simp_all [Parent.depth]
  | root => simp_all [Parent.depth]
  | via source depth =>
    simp only [he] at hi
    obtain ⟨_, _, hr, _⟩ := hi
    simp [Parent.depth, hr]

def Parents.predecessor? {g : IndexedGraph} (p : Parents g)
    (order : Enumeration g.Vertex) (target : g.Vertex) : Option g.Vertex :=
  order.states.find? (fun source => (p.get source).depth.isSome &&
    g.edge source target)

theorem Parents.predecessor?_eq {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes)
    (order : Enumeration g.Vertex) (target : g.Vertex) :
    p.predecessor? order target = Graph.predecessor? order g.successors routes target := by
  unfold predecessor? Graph.predecessor?
  congr 1
  funext source
  rw [p.isSome_iff h, edge_eq_decide]

/-- Reference synchronous parent round. This establishes the storage refinement
before replacing the round schedule by edge-frontier traversal. -/
def Parents.round {g : IndexedGraph} (p : Parents g) (order : Enumeration g.Vertex) : Parents g :=
  ⟨Array.ofFn (fun target =>
    match p.get target with
    | .unseen =>
      match p.predecessor? order target with
      | none => .unseen
      | some source => .via source ((p.get source).depth.getD 0 + 1)
    | entry => entry), by simp⟩

theorem Parents.round_represents {g : IndexedGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes) (order : Enumeration g.Vertex) :
    (p.round order).Represents (expandRouteTable order g.successors routes) := by
  intro target
  have ht := h target
  simp only [round, get, Array.getElem_ofFn]
  change (match (match p.get target with
    | .unseen => match p.predecessor? order target with
      | none => Parent.unseen
      | some source => .via source ((p.get source).depth.getD 0 + 1)
    | entry => entry) with
    | .unseen => _
    | .root => _
    | .via _ _ => _) 
  cases he : p.get target with
  | unseen =>
    simp only [he] at ht ⊢
    rw [p.predecessor?_eq h]
    cases hf : Graph.predecessor? order g.successors routes target with
    | none => simp [expandRouteTable, ht, hf]
    | some source =>
      have hraw : order.states.find? (fun candidate =>
          (routes candidate).isSome && decide (target ∈ g.successors candidate)) = some source := hf
      have hchosen := List.find?_some hraw
      have hsome : (routes source).isSome = true := (Bool.and_eq_true_iff.mp hchosen).1
      cases hr : routes source with
      | none => simp [hr] at hsome
      | some prior =>
        have hd := p.represents_depth h source hr
        have hn := p.represents_nonempty h source hr
        have hl := List.length_pos_iff.mpr hn
        refine ⟨prior, ?_, ?_, ?_⟩
        · simp [expandRouteTable, hr]
        · simp [expandRouteTable, ht, hf, hr]
        · simp only [hd, Option.getD_some]
          omega
  | root =>
    simp only [he] at ht ⊢
    simp [expandRouteTable, ht]
  | via source depth =>
    simp only [he] at ht ⊢
    obtain ⟨prior, hs, ht, hd⟩ := ht
    exact ⟨prior, by simp [expandRouteTable, hs], by simp [expandRouteTable, ht], hd⟩

def Parents.rounds (g : IndexedGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) : Nat → Parents g
  | 0 => Parents.initial g seeds
  | n + 1 => (Parents.rounds g order seeds n).round order

theorem Parents.rounds_represents (g : IndexedGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (n : Nat) :
    (Parents.rounds g order seeds n).Represents (routeTables order seeds g.successors n) := by
  induction n with
  | zero => exact Parents.initial_represents g seeds
  | succ n ih => exact Parents.round_represents _ ih order

theorem Parents.rounds_depth (g : IndexedGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (n : Nat) (i : g.Vertex) :
    ((Parents.rounds g order seeds n).get i).depth.getD 0 ≤ n := by
  induction n generalizing i with
  | zero =>
    simp only [rounds, initial, get, Array.getElem_ofFn]
    split <;> simp [Parent.depth]
  | succ n ih =>
    simp only [rounds, round, get, Array.getElem_ofFn]
    change (match (Parents.rounds g order seeds n).get i with
      | .unseen => match (Parents.rounds g order seeds n).predecessor? order i with
        | none => Parent.unseen
        | some source => .via source (((Parents.rounds g order seeds n).get source).depth.getD 0 + 1)
      | entry => entry).depth.getD 0 ≤ n + 1
    cases he : (Parents.rounds g order seeds n).get i with
    | unseen =>
      simp only [he]
      cases hf : (Parents.rounds g order seeds n).predecessor? order i with
      | none => simp [Parent.depth]
      | some source =>
        simp only [Parent.depth, Option.getD_some]
        exact Nat.add_le_add_right (ih source) 1
    | root => simp [Parent.depth]
    | via source depth =>
      have hb := ih i
      simp only [he, Parent.depth, Option.getD_some] at hb ⊢
      omega

/-- Reconstruct just the requested route from a cardinality-bounded forest. -/
def parentRoute? (g : IndexedGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) : Option (List g.Vertex) :=
  (Parents.rounds g order seeds g.size).unwind (g.size + 1) target []

theorem parentRoute?_eq (g : IndexedGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    parentRoute? g order seeds target = route? order seeds g.successors target := by
  let p := Parents.rounds g order seeds g.size
  have hr : p.Represents (routeTables order seeds g.successors g.size) :=
    Parents.rounds_represents g order seeds g.size
  simp only [parentRoute?, route?, Fintype.card_fin]
  change p.unwind (g.size + 1) target [] = routeTables order seeds g.successors g.size target
  cases ht : routeTables order seeds g.successors g.size target with
  | none =>
    have he : p.get target = .unseen := by
      have hv := hr target
      cases hc : p.get target with
      | unseen => rfl
      | root => simp [hc, ht] at hv
      | via source depth =>
        simp only [hc] at hv
        obtain ⟨_, _, hv, _⟩ := hv
        simp [ht] at hv
    simp [Parents.unwind, he]
  | some path =>
    have hn := p.represents_nonempty hr target ht
    have hl := List.length_pos_iff.mpr hn
    have hd := p.represents_depth hr target ht
    have hb := Parents.rounds_depth g order seeds g.size target
    change (p.get target).depth.getD 0 ≤ g.size at hb
    rw [hd] at hb
    simp only [Option.getD_some] at hb
    have bound : path.length ≤ g.size + 1 := by omega
    simpa using p.unwind_correct hr (g.size + 1) target [] path ht bound

end KILT.Graph.IndexedGraph
