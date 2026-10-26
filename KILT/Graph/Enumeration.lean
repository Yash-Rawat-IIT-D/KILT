import KILT.Graph.Enumeration.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.FinRange

/-! Explicit traversal orders, with executable products, subtypes and powersets. -/
namespace KILT.Graph.Enumeration
universe u v
variable {State : Type u} {Other : Type v} [DecidableEq State] [DecidableEq Other]

/-- Keep the first occurrence of each value; no ordering or classical choice. -/
def ofList (states : List State) (complete : ∀ s, s ∈ states) : Enumeration State where
  states := states.reverse.dedup.reverse
  nodup := List.nodup_reverse.mpr (List.nodup_dedup _)
  complete s := by simpa using complete s

/-- Construct from an already duplicate-free list, without running deduplication. -/
def ofNodup (states : List State) (nodup : states.Nodup)
    (complete : ∀ s, s ∈ states) : Enumeration State := ⟨states, nodup, complete⟩

/-- Exact agreement with the general constructor, including traversal order. -/
theorem ofNodup_eq_ofList (states : List State) (nodup : states.Nodup)
    (complete : ∀ s, s ∈ states) : ofNodup states nodup complete = ofList states complete := by
  simp [ofNodup, ofList, List.dedup_eq_self.mpr (List.nodup_reverse.mpr nodup)]

/-- Derive finite data locally from the supplied order. This is deliberately
not a global instance: enumeration and Fintype synthesis must not recurse. -/
def fintype (order : Enumeration State) : Fintype State where
  elems := order.states.toFinset
  complete s := by simpa using order.complete s

def product (first : Enumeration State) (second : Enumeration Other) : Enumeration (State × Other) :=
  ofNodup (first.states.flatMap fun s => second.states.map fun t => (s, t))
    (first.nodup.product second.nodup) (by
    rintro ⟨s, t⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
    exact ⟨s, first.complete s, t, second.complete t, rfl, rfl⟩)

def fin (n : Nat) : Enumeration (Fin n) :=
  ofNodup (List.finRange n) (List.nodup_finRange n) (by simp)

def subtype (order : Enumeration State) (P : State → Prop) [DecidablePred P] : Enumeration {s // P s} :=
  ofNodup ((order.states.filter fun s => decide (P s)).pmap
    (fun s hs => (⟨s, hs⟩ : {s // P s})) (by intro s hs; simpa using (List.mem_filter.mp hs).2)) (by
      apply List.Nodup.pmap (fun a ha b hb h => congrArg Subtype.val h)
      exact order.nodup.filter _) (by
    rintro ⟨s, hs⟩
    apply List.mem_pmap.mpr
    exact ⟨s, by simp [order.complete s, hs], rfl⟩)

/-- Exclude before include at each position. A duplicate-free input yields distinct subsets. -/
def subsetList : List State → List (Finset State)
  | [] => [∅]
  | s :: rest =>
      let previous := subsetList rest
      previous ++ previous.map (fun t => insert s t)

private theorem mem_subsetList (states : List State) (s : Finset State)
    (hs : ∀ a ∈ s, a ∈ states) : s ∈ subsetList states := by
  induction states generalizing s with
  | nil =>
    have heq : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by simpa using hs)
    simp [heq, subsetList]
  | cons a rest ih =>
    by_cases ha : a ∈ s
    · have hrest : s.erase a ∈ subsetList rest := ih _ (by
        intro b hb
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hb
        rcases List.mem_cons.mp (hs b hmem) with heq | htail
        · exact (hne heq).elim
        · exact htail)
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨s.erase a, hrest, Finset.insert_erase ha⟩
    · apply List.mem_append_left
      exact ih _ (by
        intro b hb
        rcases List.mem_cons.mp (hs b hb) with heq | htail
        · exact (ha (heq ▸ hb)).elim
        · exact htail)

theorem subsetList_member {states : List State} {s : Finset State}
    (hs : s ∈ subsetList states) {a : State} (ha : a ∈ s) : a ∈ states := by
  induction states generalizing s with
  | nil =>
    have he : s = ∅ := by simpa [subsetList] using hs
    subst s
    simp at ha
  | cons b rest ih =>
    simp only [subsetList, List.mem_append, List.mem_map] at hs
    rcases hs with hs | ⟨t, ht, rfl⟩
    · exact List.mem_cons_of_mem _ (ih hs ha)
    · rcases Finset.mem_insert.mp ha with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (ih ht h)

theorem subsetList_nodup {states : List State} (h : states.Nodup) :
    (subsetList states).Nodup := by
  induction states with
  | nil => simp [subsetList]
  | cons a rest ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp h
    have previous := ih hn
    rw [subsetList, List.nodup_append]
    refine ⟨previous, List.Nodup.map_on ?_ previous, ?_⟩
    · intro s hs t ht eq
      have hsa : a ∉ s := fun h => ha (subsetList_member hs h)
      have hta : a ∉ t := fun h => ha (subsetList_member ht h)
      have := congrArg (Finset.erase · a) eq
      simpa [hsa, hta] using this
    · intro s hs t ht eq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
      have : a ∈ s := eq ▸ Finset.mem_insert_self a r
      exact ha (subsetList_member hs this)

def finset (order : Enumeration State) : Enumeration (Finset State) :=
  ofNodup (subsetList order.states) (subsetList_nodup order.nodup) (fun s => mem_subsetList _ s (fun a _ => order.complete a))

/-- Evaluate an order-independent result on the finite carrier's list quotient.
No list is chosen from an unordered set: permutation invariance makes the
quotient elimination well-defined. Witness-producing APIs still take an order.
The fallback extends the lift to incomplete lists; completeness of Fintype.univ
proves that branch unreachable for this carrier. Execution failures are not caught. -/
def runInvariant [Fintype State] {Result : Type*} (fallback : Result)
    (operation : Enumeration State → Result)
    (invariant : ∀ a b, operation a = operation b) : Result :=
  Quotient.liftOn (Finset.univ : Finset State).val
    (fun xs => if h : ∀ s, s ∈ xs then operation (ofList xs h) else fallback)
    (by
      intro xs ys perm
      have complete : (∀ s, s ∈ xs) ↔ (∀ s, s ∈ ys) :=
        forall_congr' (fun s => perm.mem_iff)
      by_cases hx : ∀ s, s ∈ xs
      · rw [dif_pos hx, dif_pos (complete.mp hx)]
        exact invariant _ _
      · rw [dif_neg hx, dif_neg (fun hy => hx (complete.mpr hy))])

theorem runInvariant_eq [Fintype State] {Result : Type*} (fallback : Result)
    (operation : Enumeration State → Result)
    (invariant : ∀ a b, operation a = operation b) (specification : Result)
    (correct : ∀ order, operation order = specification) :
    runInvariant fallback operation invariant = specification := by
  unfold runInvariant
  generalize hm : (Finset.univ : Finset State).val = m
  have complete : ∀ s, s ∈ m := by intro s; rw [← hm]; simp
  induction m using Quotient.inductionOn with
  | h xs =>
    have hx : ∀ s, s ∈ xs := by simpa using complete
    simp only [Quotient.lift_mk, dif_pos hx]
    exact correct _

end KILT.Graph.Enumeration
