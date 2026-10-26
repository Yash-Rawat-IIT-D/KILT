import KILT.Graph.Acceptance

/-!
# Finite descriptions of infinite executions

A lasso visits its prefix once and repeats its nonempty loop forever. The loop
omits the duplicate closing endpoint. Graph validity is separate from data;
acceptance at the loop entry suffices for infinitely recurring acceptance.
-/
namespace KILT.Graph
universe u v

structure Lasso (State : Type u) where
  «prefix» : List State
  loop : List State
  loop_ne_nil : loop ≠ []

namespace Lasso
variable {State : Type u} {Other : Type v}

def entry (l : Lasso State) : State := l.loop.head l.loop_ne_nil

theorem loop_length_pos (l : Lasso State) : 0 < l.loop.length :=
  List.length_pos_iff.mpr l.loop_ne_nil

/-- Position zero is the first prefix state, or the loop entry for an empty prefix. -/
def sequence (l : Lasso State) : Cslib.ωSequence State := ⟨fun i =>
  if h : i < l.prefix.length then l.prefix[i]
  else l.loop[(i - l.prefix.length) % l.loop.length]'(Nat.mod_lt _ l.loop_length_pos)⟩

def replay (l : Lasso State) (count : Nat) : List State := l.sequence.take count

def map (f : State → Other) (l : Lasso State) : Lasso Other :=
  ⟨l.prefix.map f, l.loop.map f, by simpa using l.loop_ne_nil⟩

@[simp] theorem map_sequence (f : State → Other) (l : Lasso State) :
    (l.map f).sequence = l.sequence.map f := by
  ext i
  simp only [sequence, map, List.length_map, Cslib.ωSequence.get_fun,
    Cslib.ωSequence.get_map]
  split <;> simp_all

@[simp] theorem sequence_prefix_add (l : Lasso State) (n : Nat) :
    l.sequence (l.prefix.length + n) = l.loop[n % l.loop.length]'(Nat.mod_lt _ l.loop_length_pos) := by
  simp [sequence]

@[simp] theorem sequence_at_entry (l : Lasso State) :
    l.sequence l.prefix.length = l.entry := by
  simpa [entry, List.getElem_zero] using l.sequence_prefix_add 0

/-- Finite boundary checks: stem ends at the entry and loop returns to it. -/
def Valid (l : Lasso State) (seeds : Finset State) (successors : State → Finset State) : Prop :=
  (∃ s ∈ seeds, (l.prefix ++ [l.entry]).IsChainFromTo (Step successors) s l.entry) ∧
  (l.loop ++ [l.entry]).IsChainFromTo (Step successors) l.entry l.entry

private theorem sequence_eq_stem (l : Lasso State) {i : Nat} (hi : i ≤ l.prefix.length) :
    l.sequence i = (l.prefix ++ [l.entry])[i]'(by simp; omega) := by
  by_cases h : i < l.prefix.length
  · simp [sequence, h, List.getElem_append_left]
  · have : i = l.prefix.length := by omega
    subst i
    simp

private theorem loop_get_closed (l : Lasso State) {i : Nat} (hi : i ≤ l.loop.length) :
    l.loop[i % l.loop.length]'(Nat.mod_lt _ l.loop_length_pos) =
      (l.loop ++ [l.entry])[i]'(by simp; omega) := by
  by_cases h : i < l.loop.length
  · simp [Nat.mod_eq_of_lt h, List.getElem_append_left h]
  · have : i = l.loop.length := by omega
    subst i
    simp [entry, List.getElem_zero]

theorem Valid.initial {l : Lasso State} {seeds : Finset State}
    {successors : State → Finset State} (h : l.Valid seeds successors) :
    l.sequence 0 ∈ seeds := by
  obtain ⟨s, hs, hc⟩ := h.1
  rw [sequence_eq_stem l (Nat.zero_le _), hc.getElem_zero]
  exact hs

theorem Valid.step {l : Lasso State} {seeds : Finset State}
    {successors : State → Finset State} (h : l.Valid seeds successors) (i : Nat) :
    Step successors (l.sequence i) (l.sequence (i + 1)) := by
  by_cases hi : i < l.prefix.length
  · obtain ⟨s, _, hc⟩ := h.1
    rw [sequence_eq_stem l (by omega), sequence_eq_stem l (by omega)]
    exact hc.isChain.getElem i (by simp; omega)
  · let n := i - l.prefix.length
    have heq : i = l.prefix.length + n := by omega
    rw [heq, sequence_prefix_add]
    rw [show l.prefix.length + n + 1 = l.prefix.length + (n + 1) by omega,
      sequence_prefix_add]
    have hm : n % l.loop.length < l.loop.length := Nat.mod_lt _ l.loop_length_pos
    have hmod : (n + 1) % l.loop.length = (n % l.loop.length + 1) % l.loop.length := by
      simp [Nat.add_mod]
    have hc := h.2.isChain.getElem (n % l.loop.length) (by simp; omega)
    rw [← loop_get_closed l (Nat.le_of_lt hm),
      ← loop_get_closed l (show n % l.loop.length + 1 ≤ l.loop.length by omega)] at hc
    simpa only [Nat.mod_eq_of_lt hm, hmod] using hc

/-- Repeating the entry gives arbitrarily late visits, including singleton loops. -/
theorem frequently_entry (l : Lasso State) :
    ∃ᶠ i in Filter.atTop, l.sequence i = l.entry := by
  apply Filter.frequently_atTop.mpr
  intro n
  refine ⟨l.prefix.length + n * l.loop.length, ?_, ?_⟩
  · have := l.loop_length_pos
    nlinarith
  · simp [sequence_prefix_add, entry, List.getElem_zero]

theorem Valid.hasAcceptingRun {l : Lasso State} {seeds accepting : Finset State}
    {successors : State → Finset State} (h : l.Valid seeds successors)
    (ha : l.entry ∈ accepting) : HasAcceptingRun seeds successors accepting := by
  refine ⟨l.sequence, h.initial, h.step, ?_⟩
  exact l.frequently_entry.mono fun _ heq => heq ▸ ha

end Lasso
end KILT.Graph
