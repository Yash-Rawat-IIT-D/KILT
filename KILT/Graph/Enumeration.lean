import KILT.Graph.Routes
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

end KILT.Graph.Enumeration
