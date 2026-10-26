import KILT.Graph.Parents
import KILT.Graph.Specification.Rounds

/-! Stability and target stopping without storing complete routes. -/
namespace KILT.Graph.FiniteGraph

def Parents.grows {g : FiniteGraph} (previous expanded : Parents g) : Bool :=
  (List.finRange g.size).any (fun i =>
    (previous.get i).depth.isNone && (expanded.get i).depth.isSome)

theorem Parents.no_growth_fixed {g : FiniteGraph} (p : Parents g)
    {routes : RouteTable g.Vertex} (h : p.Represents routes) (order : Enumeration g.Vertex)
    (hg : p.grows (p.round order) = false) : expandRouteTable order g.successors routes = routes := by
  have hexp := p.round_represents h order
  simp only [grows, List.any_eq_false] at hg
  funext target
  cases hr : routes target with
  | some path => simp [expandRouteTable, hr]
  | none =>
    have hprev := p.isSome_iff h target
    have hnext := (p.round order).isSome_iff hexp target
    have ht := hg target (by simp)
    cases hp : (p.get target).depth <;> simp_all

def Parents.search {g : FiniteGraph} (order : Enumeration g.Vertex)
    (target : Option g.Vertex) : Nat → Parents g → Parents g
  | 0, p => p
  | fuel + 1, p =>
    if target.any (fun i => (p.get i).depth.isSome) then p else
      let expanded := p.round order
      if p.grows expanded then Parents.search order target fuel expanded else p

/-- The proof-only routes may be a stopped prefix. A full query has the full
reference table; a target query has the exact reference route at its target. -/
theorem Parents.search_spec {g : FiniteGraph} (order : Enumeration g.Vertex)
    (target : Option g.Vertex) (fuel : Nat) (p : Parents g)
    (routes : RouteTable g.Vertex) (h : p.Represents routes) :
    ∃ result, (p.search order target fuel).Represents result ∧
      (target = none → result = routeRounds order g.successors fuel routes) ∧
      (∀ q, target = some q → result q = routeRounds order g.successors fuel routes q) := by
  induction fuel generalizing p routes with
  | zero => exact ⟨routes, h, by simp [routeRounds], by simp [routeRounds]⟩
  | succ fuel ih =>
    simp only [search]
    split
    next found =>
      refine ⟨routes, h, ?_, ?_⟩
      · intro ht; simp [ht] at found
      · intro q ht
        have hsome : (routes q).isSome = true := by
          simpa [ht, p.isSome_iff h] using found
        cases hr : routes q with
        | none => simp [hr] at hsome
        | some path => exact (routeRounds_retains order g.successors (fuel + 1) routes q path hr).symm
    next =>
      split
      next growth =>
        obtain ⟨result, hrep, hfull, htarget⟩ := ih (p.round order)
          (expandRouteTable order g.successors routes) (p.round_represents h order)
        exact ⟨result, hrep, hfull, htarget⟩
      next stable =>
        have hg : p.grows (p.round order) = false := by simpa using stable
        have hf := p.no_growth_fixed h order hg
        have hall : routeRounds order g.successors (fuel + 1) routes = routes :=
          routeRounds_fixed order g.successors (fuel + 1) routes hf
        exact ⟨routes, h, fun _ => hall.symm, fun q _ => congrFun hall.symm q⟩

def parentRouteFast? (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) : Option (List g.Vertex) :=
  let p := (Parents.initial g seeds).search order (some target) g.size
  p.unwind (g.size + 1) target []

theorem parentRouteFast?_eq (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    parentRouteFast? g order seeds target = routeSpec? order seeds g.successors target := by
  let p := (Parents.initial g seeds).search order (some target) g.size
  obtain ⟨routes, hrep, _, htarget⟩ := Parents.search_spec order (some target) g.size
    (Parents.initial g seeds) (initialRouteTable seeds) (Parents.initial_represents g seeds)
  change p.Represents routes at hrep
  have ht : routes target = routeSpec? order seeds g.successors target := by
    simpa only [routeRounds_initial, routeSpec?, Fintype.card_fin] using htarget target rfl
  change p.unwind (g.size + 1) target [] = _
  cases hr : routeSpec? order seeds g.successors target with
  | none =>
    have he : p.get target = .unseen := by
      have hp := hrep target
      cases hc : p.get target with
      | unseen => rfl
      | root => simp [hc, ht, hr] at hp
      | via source depth =>
        simp only [hc] at hp
        obtain ⟨_, _, hp, _⟩ := hp
        simp [ht, hr] at hp
    simp [Parents.unwind, he]
  | some path =>
    have hp : routes target = some path := ht.trans hr
    let full := Parents.rounds g order seeds g.size
    have hfull := Parents.rounds_represents g order seeds g.size
    have hr' : routeTables order seeds g.successors g.size target = some path := by
      simpa only [routeSpec?, Fintype.card_fin] using hr
    have hn := full.represents_nonempty hfull target hr'
    have hd := full.represents_depth hfull target hr'
    have hb := Parents.rounds_depth g order seeds g.size target
    change (full.get target).depth.getD 0 ≤ g.size at hb
    rw [hd] at hb
    simp only [Option.getD_some] at hb
    have hlen := List.length_pos_iff.mpr hn
    have bound : path.length ≤ g.size + 1 := by omega
    simpa using p.unwind_correct hrep (g.size + 1) target [] path hp bound

def Parents.forest (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) : Parents g :=
  (Parents.initial g seeds).search order none g.size

theorem Parents.forest_represents (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) :
    (Parents.forest g order seeds).Represents (routeSpec? order seeds g.successors) := by
  obtain ⟨routes, hrep, hfull, _⟩ := Parents.search_spec order none g.size
    (Parents.initial g seeds) (initialRouteTable seeds) (Parents.initial_represents g seeds)
  have heq := hfull rfl
  simp only [routeRounds_initial] at heq
  subst routes
  intro i
  have hi := hrep i
  simpa only [Parents.Represents, Graph.routeSpec?, Fintype.card_fin, Parents.forest] using hi

theorem Parents.forest_unwind (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    (Parents.forest g order seeds).unwind (g.size + 1) target [] =
      routeSpec? order seeds g.successors target := by
  let p := Parents.forest g order seeds
  have hrep : p.Represents (routeSpec? order seeds g.successors) := Parents.forest_represents g order seeds
  change p.unwind (g.size + 1) target [] = _
  cases hr : routeSpec? order seeds g.successors target with
  | none =>
    have he : p.get target = .unseen := by
      have ht := hrep target
      cases hc : p.get target with
      | unseen => rfl
      | root => simp [hc, hr] at ht
      | via source depth =>
        simp only [hc] at ht
        obtain ⟨_, _, ht, _⟩ := ht
        simp [hr] at ht
    simp [Parents.unwind, he]
  | some path =>
    let full := Parents.rounds g order seeds g.size
    have hfull := Parents.rounds_represents g order seeds g.size
    have hr' : routeTables order seeds g.successors g.size target = some path := by
      simpa only [routeSpec?, Fintype.card_fin] using hr
    have hn := full.represents_nonempty hfull target hr'
    have hd := full.represents_depth hfull target hr'
    have hb := Parents.rounds_depth g order seeds g.size target
    change (full.get target).depth.getD 0 ≤ g.size at hb
    rw [hd] at hb
    simp only [Option.getD_some] at hb
    have hlen := List.length_pos_iff.mpr hn
    have bound : path.length ≤ g.size + 1 := by omega
    simpa using p.unwind_correct hrep (g.size + 1) target [] path hr bound

theorem Parents.target_isSome (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds : Finset g.Vertex) (target : g.Vertex) :
    (((Parents.initial g seeds).search order (some target) g.size).get target).depth.isSome =
      (routeSpec? order seeds g.successors target).isSome := by
  obtain ⟨routes, hrep, _, htarget⟩ := Parents.search_spec order (some target) g.size
    (Parents.initial g seeds) (initialRouteTable seeds) (Parents.initial_represents g seeds)
  have h := ((Parents.initial g seeds).search order (some target) g.size).isSome_iff hrep target
  have heq : routes target = routeSpec? order seeds g.successors target := by
    simpa only [routeRounds_initial, routeSpec?, Fintype.card_fin] using htarget target rfl
  simpa only [heq] using h

end KILT.Graph.FiniteGraph
