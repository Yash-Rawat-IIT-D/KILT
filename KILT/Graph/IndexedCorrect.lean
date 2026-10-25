import KILT.Graph.IndexedPrepare

/-! Preservation of finite paths and Büchi cycles by reachable graph storage. -/
namespace KILT.Graph.PreparedReachable
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]
variable {seeds : Finset State} {next : State → Finset State}

def decode (p : PreparedReachable seeds next) (i : p.graph.Vertex) : State :=
  p.states[i.val]'(by simpa only [p.states_size] using i.isLt)

theorem decode_injective (p : PreparedReachable seeds next) : Function.Injective p.decode := by
  intro i j h
  apply Fin.ext
  exact p.nodup.getElem_inj_iff.mp h

/-- Optional boundary lookup; traversal itself uses dense IDs. -/
def index? (p : PreparedReachable seeds next) (s : State) : Option p.graph.Vertex :=
  (denseIndex? p.states s).map (fun i => ⟨i.val, by simpa only [p.states_size] using i.isLt⟩)

theorem index?_eq_some_iff (p : PreparedReachable seeds next) (s : State)
    (i : p.graph.Vertex) : p.index? s = some i ↔ p.decode i = s := by
  simp only [index?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨j, hj, heq⟩
    have hs := (denseIndex?_eq_some_iff p.states p.nodup s j).mp hj
    cases heq
    exact hs
  · intro hs
    let j : Fin p.states.size := ⟨i.val, by simpa only [p.states_size] using i.isLt⟩
    exact ⟨j, (denseIndex?_eq_some_iff p.states p.nodup s j).mpr hs, rfl⟩

@[simp] theorem index?_decode (p : PreparedReachable seeds next) (i : p.graph.Vertex) :
    p.index? (p.decode i) = some i := (p.index?_eq_some_iff _ _).mpr rfl

/-- Filter the original witness order, rather than using discovery IDs as ties. -/
def order (p : PreparedReachable seeds next) (original : Enumeration State) : Enumeration p.graph.Vertex where
  states := original.states.filterMap p.index?
  nodup := List.Nodup.filterMap (by
    intro s t i hs ht
    have hs' := (p.index?_eq_some_iff s i).mp hs
    have ht' := (p.index?_eq_some_iff t i).mp ht
    exact hs'.symm.trans ht') original.nodup
  complete i := List.mem_filterMap.mpr ⟨p.decode i, original.complete _, p.index?_decode i⟩

theorem decode_reachable (p : PreparedReachable seeds next) (i : p.graph.Vertex) :
    Reachable seeds next (p.decode i) :=
  (p.coverage _).mp (Array.getElem_mem_toList _)

theorem exists_decode_iff (p : PreparedReachable seeds next) (s : State) :
    (∃ i, p.decode i = s) ↔ Reachable seeds next s := by
  constructor
  · rintro ⟨i, rfl⟩
    exact p.decode_reachable i
  · intro hs
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ((p.coverage s).mpr hs)
    exact ⟨⟨i, by simpa only [Array.length_toList, p.states_size] using hi⟩, heq⟩

@[simp] theorem initial_decode (p : PreparedReachable seeds next) (i : p.graph.Vertex) :
    i ∈ p.initials ↔ p.decode i ∈ seeds := p.initial_iff i

@[simp] theorem step_decode (p : PreparedReachable seeds next) (i j : p.graph.Vertex) :
    Step p.graph.successors i j ↔ Step next (p.decode i) (p.decode j) :=
  p.edge_iff i j

theorem lift_path (p : PreparedReachable seeds next) {s t : State}
    (path : Relation.ReflTransGen (Step next) s t) (i : p.graph.Vertex)
    (hi : p.decode i = s) :
    ∃ j, p.decode j = t ∧ Relation.ReflTransGen (Step p.graph.successors) i j := by
  induction path with
  | refl => exact ⟨i, hi, .refl⟩
  | @tail t u path edge ih =>
    obtain ⟨j, hj, hpath⟩ := ih
    obtain ⟨start, hstart, hreach⟩ := p.decode_reachable j
    have hu : Reachable seeds next u := ⟨start, hstart, hreach.tail (by simpa [hj] using edge)⟩
    obtain ⟨k, hk⟩ := (p.exists_decode_iff u).mpr hu
    exact ⟨k, hk, hpath.tail ((p.step_decode j k).mpr (by simpa [hj, hk] using edge))⟩

theorem path_iff (p : PreparedReachable seeds next) (i j : p.graph.Vertex) :
    Relation.ReflTransGen (Step p.graph.successors) i j ↔
      Relation.ReflTransGen (Step next) (p.decode i) (p.decode j) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail ((p.step_decode _ _).mp edge)
  · intro h
    obtain ⟨k, hk, hpath⟩ := p.lift_path h i rfl
    have heq : k = j := p.decode_injective hk
    simpa [heq] using hpath

theorem positive_path_iff (p : PreparedReachable seeds next) (i j : p.graph.Vertex) :
    Relation.TransGen (Step p.graph.successors) i j ↔
      Relation.TransGen (Step next) (p.decode i) (p.decode j) := by
  rw [Relation.TransGen.head'_iff, Relation.TransGen.head'_iff]
  constructor
  · rintro ⟨k, hedge, hpath⟩
    exact ⟨p.decode k, (p.step_decode _ _).mp hedge, (p.path_iff _ _).mp hpath⟩
  · rintro ⟨s, hedge, hpath⟩
    obtain ⟨start, hstart, hreach⟩ := p.decode_reachable i
    obtain ⟨k, hk⟩ := (p.exists_decode_iff s).mpr ⟨start, hstart, hreach.tail hedge⟩
    exact ⟨k, (p.step_decode _ _).mpr (by simpa [hk] using hedge),
      (p.path_iff _ _).mpr (by simpa [hk] using hpath)⟩

theorem reachable_iff (p : PreparedReachable seeds next) (i : p.graph.Vertex) :
    Reachable p.initials p.graph.successors i ↔ Reachable seeds next (p.decode i) := by
  constructor
  · rintro ⟨j, hj, path⟩
    exact ⟨p.decode j, (p.initial_decode j).mp hj, (p.path_iff j i).mp path⟩
  · rintro ⟨s, hs, path⟩
    obtain ⟨j, hj⟩ := (p.exists_decode_iff s).mpr ⟨s, hs, .refl⟩
    exact ⟨j, (p.initial_decode j).mpr (by simpa [hj] using hs),
      (p.path_iff j i).mpr (by simpa [hj] using path)⟩

def accepting (p : PreparedReachable seeds next) (states : Finset State) : Finset p.graph.Vertex :=
  Finset.univ.filter (fun i => p.decode i ∈ states)

@[simp] theorem mem_accepting (p : PreparedReachable seeds next) (states : Finset State)
    (i : p.graph.Vertex) : i ∈ p.accepting states ↔ p.decode i ∈ states := by
  simp [accepting]

theorem acceptingCycle_iff (p : PreparedReachable seeds next) (states : Finset State) :
    HasAcceptingCycle p.initials p.graph.successors (p.accepting states) ↔
      HasAcceptingCycle seeds next states := by
  constructor
  · rintro ⟨i, hi, hr, hp⟩
    exact ⟨p.decode i, (p.mem_accepting states i).mp hi,
      (p.reachable_iff i).mp hr, (p.positive_path_iff i i).mp hp⟩
  · rintro ⟨s, hs, hr, hp⟩
    obtain ⟨i, hi⟩ := (p.exists_decode_iff s).mpr hr
    exact ⟨i, (p.mem_accepting states i).mpr (by simpa [hi] using hs),
      (p.reachable_iff i).mpr (by simpa [hi] using hr),
      (p.positive_path_iff i i).mpr (by simpa [hi] using hp)⟩

end KILT.Graph.PreparedReachable
