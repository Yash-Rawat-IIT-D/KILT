import KILT.Graph.Search
import Cslib.Computability.Automata.NA.Basic

/-!
# Büchi acceptance in finite graphs

Acceptance means visiting accepting states arbitrarily late on an infinite
initial execution. Search reuses bounded reachability: an accepting state must
be reachable and reachable again from one of its successors. The latter test
requires a real edge, so an accepting deadlock is never a cycle witness.

The semantic proof reuses CSLib's `frequently_in_finite_type`,
`OmegaExecution.flatten_mTr`, and `OmegaExecution.append` at the pinned
CSLib revision, rather than copying their implementations:
https://github.com/leanprover/cslib/tree/a3da622f14ac47924a4ffb293fdb0dad6fcdfae1/Cslib/Foundations
-/

namespace KILT.Graph

open Filter
universe u
variable {State : Type u} [Fintype State] [DecidableEq State]

/-- An infinite initial execution visiting acceptance arbitrarily late. -/
def HasAcceptingRun (seeds : Finset State) (successors : State → Finset State)
    (accepting : Finset State) : Prop :=
  ∃ ss : Cslib.ωSequence State, ss 0 ∈ seeds ∧
    (∀ i, Step successors (ss i) (ss (i + 1))) ∧
    ∃ᶠ i in atTop, ss i ∈ accepting

/-- A reachable accepting state with a positive-length return path. -/
def HasAcceptingCycle (seeds : Finset State) (successors : State → Finset State)
    (accepting : Finset State) : Prop :=
  ∃ q ∈ accepting, Reachable seeds successors q ∧
    Relation.TransGen (Step successors) q q

/-- Search for an accepting cycle. No symbol enumeration or witness choice. -/
def hasAcceptingCycleReference (seeds : Finset State) (successors : State → Finset State)
    (accepting : Finset State) : Bool :=
  decide (((reachableSet seeds successors ∩ accepting).filter fun q =>
    q ∈ reachableSet (successors q) successors).Nonempty)

theorem hasAcceptingCycleReference_eq_true_iff (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycleReference seeds successors accepting = true ↔
      HasAcceptingCycle seeds successors accepting := by
  simp only [hasAcceptingCycleReference, decide_eq_true_eq, Finset.filter_nonempty_iff,
    Finset.mem_inter, mem_reachableSet_iff, HasAcceptingCycle]
  constructor
  · rintro ⟨q, ⟨hr, ha⟩, t, ht, hreturn⟩
    exact ⟨q, ha, hr, Relation.TransGen.head'_iff.mpr ⟨t, ht, hreturn⟩⟩
  · rintro ⟨q, ha, hr, hc⟩
    rcases Relation.TransGen.head'_iff.mp hc with ⟨t, ht, hreturn⟩
    exact ⟨q, ⟨hr, ha⟩, t, ht, hreturn⟩

/-- Short-circuit search with one successor cache shared by all return queries. -/
def acceptingCycleSearch (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) : Bool :=
  if seeds = ∅ then false else if accepting = ∅ then false else
  let edges := prepareSuccessors order successors
  let next := tableLookup ∅ edges
  let reached := reachableSetFast seeds next
  order.states.any fun q => decide (q ∈ accepting ∧ q ∈ reached) &&
    reachable? (next q) next q

theorem acceptingCycleSearch_eq (order : Enumeration State) (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    acceptingCycleSearch order seeds successors accepting =
      hasAcceptingCycleReference seeds successors accepting := by
  apply Bool.eq_iff_iff.mpr
  rw [hasAcceptingCycleReference_eq_true_iff]
  by_cases hs : seeds = ∅
  · simp [acceptingCycleSearch, hs, HasAcceptingCycle, Reachable]
  by_cases ha : accepting = ∅
  · simp [acceptingCycleSearch, ha, HasAcceptingCycle]
  have heq : tableLookup ∅ (prepareSuccessors order successors) = successors :=
    funext (prepareSuccessors_lookup order successors)
  simp only [acceptingCycleSearch, hs, ha, ↓reduceIte, heq, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, reachableSetFast_eq, mem_reachableSet_iff,
    reachable?_eq_true_iff, HasAcceptingCycle]
  constructor
  · rintro ⟨q, _, ⟨ha, hr⟩, t, ht, hreturn⟩
    exact ⟨q, ha, hr, Relation.TransGen.head'_iff.mpr ⟨t, ht, hreturn⟩⟩
  · rintro ⟨q, ha, hr, hc⟩
    exact ⟨q, order.complete q, ⟨ha, hr⟩, Relation.TransGen.head'_iff.mp hc⟩

/-- Decide accepting-cycle existence with a shared unordered cache. The bounded
existential uses Lean's short-circuit finite-set decision procedure. -/
def hasAcceptingCycle (seeds : Finset State) (successors : State → Finset State)
    (accepting : Finset State) : Bool :=
  if seeds = ∅ then false else if accepting = ∅ then false else
  let rows := prepareSuccessorSet successors
  let next := successorSetLookup rows
  let reached := reachableSetFast seeds next
  decide (∃ q ∈ reached ∩ accepting, reachable? (next q) next q = true)

theorem hasAcceptingCycle_eq_reference (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycle seeds successors accepting =
      hasAcceptingCycleReference seeds successors accepting := by
  apply Bool.eq_iff_iff.mpr
  rw [hasAcceptingCycleReference_eq_true_iff]
  by_cases hs : seeds = ∅
  · simp [hasAcceptingCycle, hs, HasAcceptingCycle, Reachable]
  by_cases ha : accepting = ∅
  · simp [hasAcceptingCycle, ha, HasAcceptingCycle]
  have heq : successorSetLookup (prepareSuccessorSet successors) = successors :=
    funext (prepareSuccessorSet_lookup successors)
  simp only [hasAcceptingCycle, hs, ha, ↓reduceIte, heq, decide_eq_true_eq,
    reachableSetFast_eq, Finset.mem_inter, mem_reachableSet_iff, reachable?_eq_true_iff,
    HasAcceptingCycle]
  constructor
  · rintro ⟨q, ⟨hr, ha⟩, t, ht, hreturn⟩
    exact ⟨q, ha, hr, Relation.TransGen.head'_iff.mpr ⟨t, ht, hreturn⟩⟩
  · rintro ⟨q, ha, hr, hc⟩
    exact ⟨q, ⟨hr, ha⟩, Relation.TransGen.head'_iff.mp hc⟩

theorem hasAcceptingCycle_eq_true_iff (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycle seeds successors accepting = true ↔
      HasAcceptingCycle seeds successors accepting := by
  rw [hasAcceptingCycle_eq_reference, hasAcceptingCycleReference_eq_true_iff]

omit [Fintype State] [DecidableEq State] in
/-- Every finite segment of a valid sequence is reachable. -/
theorem sequence_reachable {ss : Cslib.ωSequence State}
    {successors : State → Finset State}
    (valid : ∀ i, Step successors (ss i) (ss (i + 1)))
    {i j : Nat} (hij : i ≤ j) :
    Relation.ReflTransGen (Step successors) (ss i) (ss j) := by
  induction j, hij using Nat.le_induction with
  | base => exact .refl
  | succ j _ ih => exact .tail ih (valid j)

private def unitLTS (successors : State → Finset State) : Cslib.LTS State Unit where
  Tr s _ t := Step successors s t

omit [Fintype State] [DecidableEq State] in
private theorem reachable_mTr {successors : State → Finset State} {s t : State}
    (h : Relation.ReflTransGen (Step successors) s t) :
    ∃ labels, (unitLTS successors).MTr s labels t := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | tail _ hedge ih =>
    rcases ih with ⟨labels, hlabels⟩
    exact ⟨labels ++ [()], hlabels.stepR (unitLTS successors) hedge⟩

omit [DecidableEq State] in
/-- The finite accepting-cycle criterion is exactly infinite Büchi acceptance.
Classical selection here constructs a semantic existence witness only. -/
theorem hasAcceptingCycle_iff_hasAcceptingRun (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    HasAcceptingCycle seeds successors accepting ↔
      HasAcceptingRun seeds successors accepting := by
  classical
  constructor
  · rintro ⟨q, hacc, hreach, hcycle⟩
    rcases hreach with ⟨s, hseed, hprefix⟩
    rcases Relation.TransGen.head'_iff.mp hcycle with ⟨t, hedge, hreturn⟩
    rcases reachable_mTr hreturn with ⟨labels, hlabels⟩
    let blocks : Cslib.ωSequence (List Unit) := Cslib.ωSequence.const (() :: labels)
    have hpos : ∀ k, 0 < (blocks k).length := by intro k; simp [blocks]
    have hblocks : ∀ k, (unitLTS successors).MTr
        ((Cslib.ωSequence.const q) k) (blocks k)
        ((Cslib.ωSequence.const q) (k + 1)) := by
      intro k
      exact .stepL hedge hlabels
    obtain ⟨loop, hloop, hvisit⟩ := Cslib.LTS.OmegaExecution.flatten_mTr hblocks hpos
    have hzero : loop 0 = q := by simpa using hvisit 0
    rcases reachable_mTr hprefix with ⟨stem, hprefix⟩
    obtain ⟨ss, hss, hstart, _, hdrop⟩ :=
      Cslib.LTS.OmegaExecution.append hprefix hloop hzero
    refine ⟨ss, hstart ▸ hseed, hss, frequently_atTop.mpr ?_⟩
    intro n
    have hbound : n ≤ blocks.cumLen n := by
      have h := (Cslib.ωSequence.cumLen_strictMono hpos).id_le n
      exact h
    refine ⟨blocks.cumLen n + stem.length, by omega, ?_⟩
    have heq := congrArg (fun xs : Cslib.ωSequence State => xs (blocks.cumLen n)) hdrop
    change ss (blocks.cumLen n + stem.length) = loop (blocks.cumLen n) at heq
    rw [heq, hvisit]
    exact hacc
  · rintro ⟨ss, hseed, hvalid, hfrequent⟩
    obtain ⟨q, hacc, hq⟩ := Cslib.ωSequence.frequently_in_finite_type.mp hfrequent
    obtain ⟨i, _, hi⟩ := frequently_atTop.mp hq 0
    obtain ⟨j, hj, heq⟩ := frequently_atTop.mp hq (i + 1)
    refine ⟨q, hacc, ⟨ss 0, hseed, ?_⟩, ?_⟩
    · simpa [hi] using sequence_reachable hvalid (Nat.zero_le i)
    · apply Relation.TransGen.head'_iff.mpr
      refine ⟨ss (i + 1), ?_, ?_⟩
      · simpa [hi] using hvalid i
      · simpa [heq] using sequence_reachable hvalid hj

theorem hasAcceptingCycle_eq_true_iff_run (seeds : Finset State)
    (successors : State → Finset State) (accepting : Finset State) :
    hasAcceptingCycle seeds successors accepting = true ↔
      HasAcceptingRun seeds successors accepting :=
  (hasAcceptingCycle_eq_true_iff seeds successors accepting).trans
    (hasAcceptingCycle_iff_hasAcceptingRun seeds successors accepting)

end KILT.Graph
