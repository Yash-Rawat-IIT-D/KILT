import KILT.Automata.GeneralizedBuchi
import KILT.Automata.Product

/-! # Correctness of generalized Büchi conversion
Run lifting is deterministic. The only recurrence argument is the bounded
round-robin lemma; neither direction assumes total transitions.
-/
namespace KILT.Automata.FiniteGeneralizedBuchi
open Filter Cslib Cslib.Automata
universe u v
variable {Q : Type u} {Symbol : Type v} [Fintype Q] [DecidableEq Q]

private theorem advance_stay (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter)
    (h : q ∉ A.accepting[i.val]?.getD ∅) : A.advance q i = i := by
  simp [advance, hit, h]

private theorem advance_move (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter)
    (hn : 0 < A.accepting.length) (h : q ∈ A.accepting[i.val]?.getD ∅) :
    (A.advance q i).val = if i.val + 1 < A.accepting.length then i.val + 1 else 0 := by
  have hm : max 1 A.accepting.length = A.accepting.length := by omega
  simp only [advance, hit, decide_eq_true h, ↓reduceIte]
  simp only [hm]
  split <;> simp_all [zero]

/-- Acceptance equivalence for any sequence obeying the counter recurrence. -/
theorem counter_acceptance (A : FiniteGeneralizedBuchi Q Symbol)
    (ss : Cslib.ωSequence Q) (cs : Nat → A.Counter)
    (step : ∀ k, cs (k+1) = A.advance (ss k) (cs k)) :
    (∃ᶠ k in atTop, (ss k, cs k) ∈ A.toFiniteBuchi.accepting) ↔
      ∀ F ∈ A.accepting, ∃ᶠ k in atTop, ss k ∈ F := by
  by_cases hempty : A.accepting = []
  · simp [converted_accept, hempty]
    infer_instance
  have hn : 0 < A.accepting.length := List.length_pos_iff.mpr hempty
  have hm : max 1 A.accepting.length = A.accepting.length := by omega
  have hb k : (cs k).val < A.accepting.length := by simpa [hm] using (cs k).isLt
  let P : Nat → Nat → Prop := fun k i => ss k ∈ A.accepting[i]?.getD ∅
  have stay k (h : ¬ P k (cs k).val) : (cs (k+1)).val = (cs k).val := by
    rw [step k, advance_stay A _ _ h]
  have move k (h : P k (cs k).val) : (cs (k+1)).val =
      if (cs k).val + 1 < A.accepting.length then (cs k).val + 1 else 0 := by
    rw [step k]; exact advance_move A _ _ hn h
  have hz k : ((ss k, cs k) ∈ A.toFiniteBuchi.accepting) ↔
      (cs k).val = 0 ∧ P k 0 := by
    rw [converted_accept, or_iff_right hempty]
    simp only [hit, decide_eq_true_eq]
    constructor
    · rintro ⟨hc, hp⟩; exact ⟨congrArg Fin.val hc, by simpa [hc, zero, P] using hp⟩
    · rintro ⟨hc, hp⟩
      have he : cs k = A.zero := Fin.ext hc
      exact ⟨he, by simpa [hc, P] using hp⟩
  constructor
  · intro h F hF
    have hf := RoundRobin.sound hn stay move (h.mono fun k hk => (hz k).mp hk)
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hF
    simpa [P, List.getElem?_eq_getElem hi, he] using hf i hi
  · intro h
    have hf : ∀ i < A.accepting.length, ∃ᶠ k in atTop, P k i := by
      intro i hi
      simpa [P, List.getElem?_eq_getElem hi] using h _ (List.getElem_mem hi)
    exact (RoundRobin.complete hn hb stay move hf).mono fun k hk => (hz k).mpr hk

/-- Deterministic lifting preserves and reflects acceptance of an original run. -/
theorem lift_acceptingRun (A : FiniteGeneralizedBuchi Q Symbol)
    {word : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence Q}
    (h : A.toNA.Run word ss) :
    (∃ᶠ k in atTop, A.liftSequence ss k ∈ A.toFiniteBuchi.accepting) ↔
      A.AcceptingRun word ss := by
  exact (A.counter_acceptance ss (A.counter ss) (fun _ => rfl)).trans
    (and_iff_right h).symm

/-- Conversion preserves the accepted infinite-word language. -/
theorem toFiniteBuchi_accepts (A : FiniteGeneralizedBuchi Q Symbol)
    (word : Cslib.ωSequence Symbol) :
    ωAcceptor.Accepts A.toFiniteBuchi.toCSLib word ↔ A.Accepts word := by
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    refine ⟨fun k => (ss k).1, A.project_run hrun, ?_⟩
    have step k := ((A.converted_transition _ _ _).mp (hrun.trans k)).2
    exact (A.counter_acceptance (fun k => (ss k).1) (fun k => (ss k).2) step).mp
      (by simpa using hacc)
  · rintro ⟨ss, hrun, hacc⟩
    exact ⟨A.liftSequence ss, A.lift_run hrun,
      (A.lift_acceptingRun hrun).mpr ⟨hrun, hacc⟩⟩

end KILT.Automata.FiniteGeneralizedBuchi

namespace KILT.FiniteKripke
open Automata Cslib Cslib.Automata
universe u v w
variable {State : Type u} {AP : Type v} {Q : Type w}
variable [Fintype State] [DecidableEq State] [Fintype Q] [DecidableEq Q]

/-- Existing search decides existence of a path meeting every recurring obligation. -/
theorem hasAcceptedPath_generalized_iff (M : FiniteKripke State AP)
    (A : FiniteGeneralizedBuchi Q (LTL.Valuation AP)) :
    M.hasAcceptedPath A.toFiniteBuchi = true ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ A.Accepts p.word := by
  rw [hasAcceptedPath_eq_true_iff]
  exact exists_congr fun p => and_congr_right fun _ => A.toFiniteBuchi_accepts p.word
end KILT.FiniteKripke
