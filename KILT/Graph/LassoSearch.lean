import KILT.Graph.Lasso
import KILT.Graph.StoredRoutes

/-!
# Accepting lasso extraction

Scan reachable accepting entries in explicit order. A return route starts from
an immediate successor, enforcing a positive-length cycle. Materialized rounds
reuse the existing bounded route algorithm and retain its tie-breaking choices.
-/
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
      let returns := storedRoutes order (successors q) successors
      (tableLookup none returns q).map fun back =>
        ⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩
  else none

private theorem candidate_isSome (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) (q : State) :
    (candidateLasso? order successors accepting (route? order seeds successors) q).isSome = true ↔
      q ∈ accepting ∧ Reachable seeds successors q ∧ Reachable (successors q) successors q := by
  rw [← route?_isSome_iff order seeds successors q,
    ← route?_isSome_iff order (successors q) successors q]
  by_cases ha : q ∈ accepting
  · cases hs : route? order seeds successors q <;>
      cases hb : route? order (successors q) successors q <;>
      simp [candidateLasso?, ha, hs, hb]
  · simp [candidateLasso?, ha]

private theorem candidate_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State)
    (q : State) {l : Lasso State}
    (h : candidateLasso? order successors accepting (route? order seeds successors) q = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  by_cases ha : q ∈ accepting
  · cases hs : route? order seeds successors q with
    | none => simp [candidateLasso?, ha, hs] at h
    | some stem =>
      cases hb : route? order (successors q) successors q with
      | none => simp [candidateLasso?, ha, hs, hb] at h
      | some back =>
        simp only [candidateLasso?, ite_eq_left ha, hs, storedRoutes_lookup, hb,
          Option.map_some, Option.some.injEq] at h
        subst l
        obtain ⟨s, hseed, hstem⟩ := route?_sound order seeds successors hs
        obtain ⟨t, hedge, hback⟩ := route?_sound order (successors q) successors hb
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

/-- Return one accepting lasso, retaining the supplied order's route choices. -/
def acceptingLasso? (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) : Option (Lasso State) :=
  let edges := materialize order successors
  let next := tableLookup ∅ edges
  let stems := storedRoutes order seeds next
  order.states.findSome? (candidateLasso? order next accepting (tableLookup none stems))

private theorem acceptingLasso?_reference (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    acceptingLasso? order seeds successors accepting =
      order.states.findSome? (candidateLasso? order successors accepting (route? order seeds successors)) := by
  have heq : tableLookup ∅ (materialize order successors) = successors :=
    funext fun s => tableLookup_materialize _ _ _ s
  have hr : tableLookup none (storedRoutes order seeds successors) = route? order seeds successors :=
    funext fun s => storedRoutes_lookup _ _ _ s
  simp only [acceptingLasso?, heq, hr]

theorem acceptingLasso?_sound (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) {l : Lasso State}
    (h : acceptingLasso? order seeds successors accepting = some l) :
    l.Valid seeds successors ∧ l.entry ∈ accepting := by
  rw [acceptingLasso?_reference] at h
  obtain ⟨_, q, _, _, hq, _⟩ := List.findSome?_eq_some_iff.mp h
  exact candidate_sound order seeds successors accepting q hq

theorem acceptingLasso?_isSome_iff (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? order seeds successors accepting).isSome = true ↔
      hasAcceptingCycle seeds successors accepting = true := by
  rw [acceptingLasso?_reference, List.isSome_findSome?, List.any_eq_true,
    hasAcceptingCycle_eq_true_iff]
  simp only [candidate_isSome, HasAcceptingCycle]
  constructor
  · rintro ⟨q, _, ha, hr, t, ht, hreturn⟩
    exact ⟨q, ha, hr, Relation.TransGen.head'_iff.mpr ⟨t, ht, hreturn⟩⟩
  · rintro ⟨q, ha, hr, hc⟩
    exact ⟨q, order.complete q, ha, hr, Relation.TransGen.head'_iff.mp hc⟩

theorem acceptingLasso?_iff_run (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? order seeds successors accepting).isSome = true ↔
      HasAcceptingRun seeds successors accepting :=
  (acceptingLasso?_isSome_iff order seeds successors accepting).trans
    (hasAcceptingCycle_eq_true_iff_run seeds successors accepting)

theorem acceptingLasso?_order_independent (first second : Enumeration State)
    (seeds : Finset State) (successors : State → Finset State) (accepting : Finset State) :
    (acceptingLasso? first seeds successors accepting).isSome =
      (acceptingLasso? second seeds successors accepting).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [acceptingLasso?_isSome_iff, acceptingLasso?_isSome_iff]

end KILT.Graph
