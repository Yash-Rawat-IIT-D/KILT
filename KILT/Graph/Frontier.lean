import KILT.Graph.ParentSearch

/-!
# Level-frontier parent expansion

Earlier-level states cannot be predecessors of an undiscovered target: their
edges already supplied routes in earlier rounds. Restricting predecessor scans
to the current level therefore preserves the exact enumeration tie-breaker.
-/
namespace KILT.Graph.FiniteGraph

theorem Parents.ext_get {g : FiniteGraph} {p q : Parents g}
    (h : ∀ i, p.get i = q.get i) : p = q := by
  cases p with
  | mk a ha =>
    cases q with
    | mk b hb =>
      have heq : a = b := by
        apply Array.ext
        · omega
        · intro i hi hj
          exact h ⟨i, by omega⟩
      cases heq
      rfl

theorem Parents.unseen_predecessor_depth (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (n : Nat) (target source : g.Vertex) (depth : Nat)
    (ht : (Parents.rounds g order seeds n).get target = .unseen)
    (hs : ((Parents.rounds g order seeds n).get source).depth = some depth)
    (edge : target ∈ g.successors source) : depth = n := by
  let p := Parents.rounds g order seeds n
  have hrep := Parents.rounds_represents g order seeds n
  have hb := Parents.rounds_depth g order seeds n source
  have hnone := hrep target
  change (match p.get target with
    | .unseen => _
    | .root => _
    | .via _ _ => _) at hnone
  change p.get target = .unseen at ht
  simp only [ht] at hnone
  change (p.get source).depth.getD 0 ≤ n at hb
  change (p.get source).depth = some depth at hs
  simp only [hs, Option.getD_some] at hb
  by_contra hne
  have hlt : depth < n := by omega
  have hsome := p.isSome_iff hrep source
  have hroute : (routeTables order seeds g.successors n source).isSome = true := by
    simpa only [hs, Option.isSome_some] using hsome.symm
  cases hr : routeTables order seeds g.successors n source with
  | none => simp [hr] at hroute
  | some path =>
    obtain ⟨initial, hinitial, chain⟩ := routeTables_valid order seeds g.successors hr
    have hd := p.represents_depth hrep source hr
    rw [hs] at hd
    have hd' : path.length - 1 = depth := (Option.some.inj hd).symm
    have steps := chain.relatesInSteps (n := depth) (by have := chain.length_pos; omega)
    have reached : target ∈ layers seeds g.successors n :=
      mem_layers_iff.mpr ⟨initial, hinitial, depth + 1, by omega,
        Relation.RelatesInSteps.tail _ _ _ _ steps edge⟩
    have hc := (routeTables_isSome_iff_mem_layers order seeds g.successors n target).mpr reached
    simp [hnone] at hc

def Parents.frontierRound {g : FiniteGraph} (p : Parents g)
    (order : Enumeration g.Vertex) (n : Nat) : Parents g :=
  let frontier := order.states.filter (fun i => (p.get i).depth == some n)
  ⟨Array.ofFn (fun target =>
    match p.get target with
    | .unseen =>
      match frontier.find? (fun source => g.edge source target) with
      | none => .unseen
      | some source => .via source (n + 1)
    | entry => entry), by simp⟩

theorem Parents.frontierRound_eq (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (n : Nat) :
    (Parents.rounds g order seeds n).frontierRound order n =
      (Parents.rounds g order seeds n).round order := by
  let p := Parents.rounds g order seeds n
  apply Parents.ext_get
  intro target
  change ((p.frontierRound order n).get target) = (p.round order).get target
  simp only [frontierRound, round, get, Array.getElem_ofFn, edge_eq_decide]
  change (match p.get target with
    | .unseen => match (order.states.filter (fun i => (p.get i).depth == some n)).find?
      (fun source => decide (target ∈ g.successors source)) with
      | none => Parent.unseen
      | some source => .via source (n + 1)
    | entry => entry) = (match p.get target with
    | .unseen => match p.predecessor? order target with
      | none => Parent.unseen
      | some source => .via source ((p.get source).depth.getD 0 + 1)
    | entry => entry)
  cases ht : p.get target with
  | root => rfl
  | via source depth => rfl
  | unseen =>
    simp only [ht]
    have predicates : (fun source => ((p.get source).depth == some n) &&
        decide (target ∈ g.successors source)) =
        (fun source => (p.get source).depth.isSome && decide (target ∈ g.successors source)) := by
      funext source
      by_cases he : target ∈ g.successors source
      · cases hs : (p.get source).depth with
        | none => simp [hs]
        | some depth =>
          have hd := Parents.unseen_predecessor_depth g order seeds n target source depth ht hs he
          simp [hs, hd]
      · simp [he]
    rw [List.find?_filter]
    simp only [Bool.decide_and, Bool.decide_eq_true]
    rw [predicates]
    have hfind : order.states.find? (fun source => (p.get source).depth.isSome &&
        decide (target ∈ g.successors source)) = p.predecessor? order target := by
      simp only [Parents.predecessor?, edge_eq_decide]
    rw [hfind]
    change (match p.predecessor? order target with
      | none => Parent.unseen
      | some source => .via source (n + 1)) = _
    cases hf : p.predecessor? order target with
    | none => rfl
    | some source =>
      have hc := List.find?_some hf
      have he : target ∈ g.successors source := by
        simpa only [edge_eq_decide, decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hc).2
      have hs : (p.get source).depth.isSome = true := (Bool.and_eq_true_iff.mp hc).1
      cases hd : (p.get source).depth with
      | none => simp [hd] at hs
      | some depth =>
        have hdepth := Parents.unseen_predecessor_depth g order seeds n target source depth ht hd he
        simp [hd, hdepth]

def Parents.frontierSearch {g : FiniteGraph} (order : Enumeration g.Vertex)
    (target : Option g.Vertex) : Nat → Nat → Parents g → Parents g
  | 0, _, p => p
  | fuel + 1, n, p =>
    if target.any (fun i => (p.get i).depth.isSome) then p else
      let expanded := p.frontierRound order n
      if p.grows expanded then Parents.frontierSearch order target fuel (n + 1) expanded else p

theorem Parents.frontierSearch_eq (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : Option g.Vertex) (fuel n : Nat) :
    (Parents.rounds g order seeds n).frontierSearch order target fuel n =
      (Parents.rounds g order seeds n).search order target fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [frontierSearch, search]
    rw [Parents.frontierRound_eq]
    split
    · rfl
    · split
      · exact ih (n + 1)
      · rfl

def Parents.frontierForest (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) : Parents g :=
  (Parents.initial g seeds).frontierSearch order none g.size 0

theorem Parents.frontierForest_eq (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) :
    Parents.frontierForest g order seeds = Parents.forest g order seeds :=
  Parents.frontierSearch_eq g order seeds none g.size 0

theorem Parents.frontierTarget_eq (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    (Parents.initial g seeds).frontierSearch order (some target) g.size 0 =
      (Parents.initial g seeds).search order (some target) g.size :=
  Parents.frontierSearch_eq g order seeds (some target) g.size 0

end KILT.Graph.FiniteGraph
