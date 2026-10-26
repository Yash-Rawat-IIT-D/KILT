import KILT.Graph.Specification.Routes
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

def product (first : Enumeration State) (second : Enumeration Other) : Enumeration (State × Other) :=
  ofList (first.states.flatMap fun s => second.states.map fun t => (s, t)) (by
    rintro ⟨s, t⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
    exact ⟨s, first.complete s, t, second.complete t, rfl, rfl⟩)

def fin (n : Nat) : Enumeration (Fin n) := ofList (List.finRange n) (by simp)

def subtype (order : Enumeration State) (P : State → Prop) [DecidablePred P] : Enumeration {s // P s} :=
  ofList ((order.states.filter fun s => decide (P s)).pmap
    (fun s hs => (⟨s, hs⟩ : {s // P s})) (by intro s hs; simpa using (List.mem_filter.mp hs).2)) (by
    rintro ⟨s, hs⟩
    apply List.mem_pmap.mpr
    exact ⟨s, by simp [order.complete s, hs], rfl⟩)

/-- Exclude before include at each position; duplicates, if any, are removed by ofList. -/
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

def finset (order : Enumeration State) : Enumeration (Finset State) :=
  ofList (subsetList order.states) (fun s => mem_subsetList _ s (fun a _ => order.complete a))

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
