import KILT.Graph.Lasso
import KILT.Graph.Specification.Routes

/-! Deterministic mathematical selection contract; no caches or stored route tables. -/
namespace KILT.Graph
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

private def candidateLasso? (order : Enumeration State)
    (successors : State → Finset State) (accepting : Finset State)
    (stems : RouteTable State) (q : State) : Option (Lasso State) :=
  if q ∈ accepting then
    match stems q with
    | none => none
    | some stem =>
      (routeSpec? order (successors q) successors q).map fun back =>
        ⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩
  else none

private theorem candidate_isSome (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) (q : State) :
    (candidateLasso? order successors accepting (routeSpec? order seeds successors) q).isSome = true ↔
      q ∈ accepting ∧ Reachable seeds successors q ∧ Reachable (successors q) successors q := by
  rw [← routeSpec?_isSome_iff order seeds successors q,
    ← routeSpec?_isSome_iff order (successors q) successors q]
  by_cases ha : q ∈ accepting
  · cases hs : routeSpec? order seeds successors q <;>
      cases hb : routeSpec? order (successors q) successors q <;>
      simp [candidateLasso?, ha, hs, hb]
  · simp [candidateLasso?, ha]

private theorem candidate_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State)
    (q : State) {l : Lasso State}
    (h : candidateLasso? order successors accepting (routeSpec? order seeds successors) q = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  by_cases ha : q ∈ accepting
  · cases hs : routeSpec? order seeds successors q with
    | none => simp [candidateLasso?, ha, hs] at h
    | some stem =>
      cases hb : routeSpec? order (successors q) successors q with
      | none => simp [candidateLasso?, ha, hs, hb] at h
      | some back =>
        simp only [candidateLasso?, ite_eq_left ha, hs, hb,
          Option.map_some, Option.some.injEq] at h
        subst l
        obtain ⟨s, hseed, hstem⟩ := routeSpec?_sound order seeds successors hs
        obtain ⟨t, hedge, hback⟩ := routeSpec?_sound order (successors q) successors hb
        have heq : stem.dropLast ++ [q] = stem := by
          simpa [hstem.getLast_eq] using stem.dropLast_append_getLast hstem.ne_nil
        have heq' : back.dropLast ++ [q] = back := by
          simpa [hback.getLast_eq] using back.dropLast_append_getLast hback.ne_nil
        refine ⟨?_, ha⟩
        change (∃ s ∈ seeds, (stem.dropLast ++ [q]).IsChainFromTo (Step successors) s q) ∧
          ((q :: back.dropLast) ++ [q]).IsChainFromTo (Step successors) q q
        constructor
        · exact ⟨s, hseed, heq.symm ▸ hstem⟩
        · simpa only [List.cons_append, heq'] using hback.cons hedge
  · simp [candidateLasso?, ha] at h

/-- Deterministic lasso-selection specification. Production extraction uses parents. -/
def lassoSpec? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) : Option (Lasso State) :=
  order.states.findSome? (candidateLasso? order successors accepting (routeSpec? order seeds successors))

/-- Expose the selection recurrence for representation proofs. -/
theorem lassoSpec?_eq_findSome (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    lassoSpec? order seeds successors accepting = order.states.findSome? (fun q =>
      if q ∈ accepting then
        (routeSpec? order seeds successors q).bind fun stem =>
          (routeSpec? order (successors q) successors q).map fun back =>
            (⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩ : Lasso State)
      else none) := by
  unfold lassoSpec?
  congr 1
  funext q
  simp only [candidateLasso?]
  split
  · cases routeSpec? order seeds successors q <;> rfl
  · rfl

theorem lassoSpec?_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) {l : Lasso State}
    (h : lassoSpec? order seeds successors accepting = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  change order.states.findSome? _ = some l at h
  obtain ⟨_, q, _, _, hq, _⟩ := List.findSome?_eq_some_iff.mp h
  exact candidate_sound order seeds successors accepting q hq

theorem lassoSpec?_isSome_iff (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (lassoSpec? order seeds successors accepting).isSome = true ↔
      HasAcceptingCycle seeds successors accepting := by
  rw [lassoSpec?, List.isSome_findSome?, List.any_eq_true]
  simp only [candidate_isSome, HasAcceptingCycle]
  constructor
  · rintro ⟨q, _, ha, hr, t, ht, hreturn⟩
    exact ⟨q, ha, hr, Relation.TransGen.head'_iff.mpr ⟨t, ht, hreturn⟩⟩
  · rintro ⟨q, ha, hr, hc⟩
    exact ⟨q, order.complete q, ha, hr, Relation.TransGen.head'_iff.mp hc⟩

theorem lassoSpec?_empty (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State)
    (h : seeds = ∅ ∨ accepting = ∅) : lassoSpec? order seeds successors accepting = none := by
  apply List.findSome?_eq_none_iff.mpr
  intro q _
  cases hc : candidateLasso? order successors accepting (routeSpec? order seeds successors) q with
  | none => rfl
  | some l =>
    have hs := (candidate_isSome order seeds successors accepting q).mp (by simp [hc])
    rcases h with h | h
    · simpa [h, Reachable] using hs.2.1
    · simpa [h] using hs.1

end KILT.Graph
