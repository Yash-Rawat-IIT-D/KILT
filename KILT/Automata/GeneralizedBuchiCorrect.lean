import KILT.Automata.GeneralizedBuchi
import KILT.Automata.Product

/-!
# Correctness of generalized Büchi conversion

This module connects the abstract round-robin recurrence proof to automaton
acceptance and then to executable checking on finite Kripke structures. It
justifies replacing a finite family of generalized Büchi obligations with one
ordinary Büchi acceptance condition on states paired with a counter.

The correctness bridge has three stages:

* `counter_acceptance` instantiates `RoundRobin.sound` and `RoundRobin.complete`
  with the actual counter update: recurring converted acceptance is equivalent
  to visiting every original accepting set infinitely often.
* `lift_acceptingRun` and `toFiniteBuchi_accepts` combine that recurrence result
  with run lifting and projection. The converted `FiniteBuchi`, viewed through
  CSLib's Büchi interface, accepts exactly the original generalized language.
* `KILT.FiniteKripke.hasAcceptedPath_generalized_iff` transports this language
  equivalence through the existing product/search correctness theorem. The
  ordinary Büchi checker can therefore decide whether an initial Kripke path
  has a word accepted by the generalized automaton.

For the LTL pipeline, this bridge lets the tableau's separate until obligations
use the existing ordinary Büchi emptiness machinery. The connection between
tableau acceptance and LTL trace semantics is proved separately. No direction
here assumes total automaton transitions: acceptance always requires a valid
infinite run, including when the family of accepting sets is empty.
-/
namespace KILT.Automata.FiniteGeneralizedBuchi
open Filter Cslib Cslib.Automata
universe u v
variable {Q : Type u} {Symbol : Type v} [Fintype Q] [DecidableEq Q]

/-- When the current state misses the accepting set selected by the counter,
the counter stays put. This supplies the waiting rule used to instantiate the
abstract round-robin recurrence theorem in `counter_acceptance`. -/
private theorem advance_stay (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter)
    (h : q ∉ A.accepting[i.val]?.getD ∅) : A.advance q i = i := by
  simp [advance, hit, h]

/-- For a nonempty acceptance family, hitting the selected set advances to the
next obligation, wrapping to zero after the last. Together with `advance_stay`,
this identifies the concrete update with the cyclic counter of `RoundRobin`. -/
private theorem advance_move (A : FiniteGeneralizedBuchi Q Symbol) (q : Q) (i : A.Counter)
    (hn : 0 < A.accepting.length) (h : q ∈ A.accepting[i.val]?.getD ∅) :
    (A.advance q i).val = if i.val + 1 < A.accepting.length then i.val + 1 else 0 := by
  have hm : max 1 A.accepting.length = A.accepting.length := by omega
  simp only [advance, hit, decide_eq_true h, ↓reduceIte]
  simp only [hm]
  split <;> simp_all [zero]

/-- The recurrence core of the conversion: a state sequence paired with any
counter sequence obeying `advance` visits the converted Büchi accepting set
infinitely often iff the original sequence visits every generalized accepting
set infinitely often. Neither a valid automaton run nor initial counter zero is
needed for this recurrence statement.

For a nonempty family, converted acceptance means a selected hit of obligation
zero; its infinite recurrence is equivalent to infinitely many counter rounds.
`RoundRobin.sound` and `RoundRobin.complete` prove the two directions. For an
empty family, both recurrence conditions are vacuous. Later theorems add run
validity to obtain acceptance and language equivalence. -/
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

/-- For an already valid original run, adding its canonical counter annotation
satisfies the converted Büchi recurrence condition iff the original run is
generalized accepting. This specializes `counter_acceptance` to `A.counter ss`;
the separate `lift_run` theorem supplies validity of the lifted run. It is the
acceptance step used when constructing an accepting converted run. -/
theorem lift_acceptingRun (A : FiniteGeneralizedBuchi Q Symbol)
    {word : Cslib.ωSequence Symbol} {ss : Cslib.ωSequence Q}
    (h : A.toNA.Run word ss) :
    (∃ᶠ k in atTop, A.liftSequence ss k ∈ A.toFiniteBuchi.accepting) ↔
      A.AcceptingRun word ss := by
  exact (A.counter_acceptance ss (A.counter ss) (fun _ => rfl)).trans
    (and_iff_right h).symm

/-- The converted ordinary Büchi automaton, interpreted through CSLib's
`ωAcceptor.Accepts`, accepts exactly the words accepted by the original
generalized Büchi automaton.

An accepting converted run projects to an original run, and its counter
recurrence gives generalized acceptance via `counter_acceptance`. Conversely,
an original accepting run lifts deterministically to an accepting converted
run. This language equivalence allows later checking stages to replace
generalized acceptance with ordinary Büchi acceptance without losing or adding
accepted words. -/
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

/-- Running the existing finite Kripke checker with the converted Büchi
automaton returns `true` iff some initial infinite Kripke path has an observed
word accepted by the original generalized automaton.

This combines ordinary Büchi product/search correctness
(`hasAcceptedPath_eq_true_iff`) with `toFiniteBuchi_accepts`. It makes the
generalized acceptance conditions, including the tableau's until obligations,
usable through the existing executable search without a separate generalized
Büchi emptiness algorithm. The statement is existential over initial paths;
the later LTL checking layer applies it to the automaton for violations. -/
theorem hasAcceptedPath_generalized_iff (M : FiniteKripke State AP)
    (A : FiniteGeneralizedBuchi Q (LTL.Valuation AP)) :
    M.hasAcceptedPath A.toFiniteBuchi = true ↔
      ∃ p : M.toKripke.Path, p.IsInitial ∧ A.Accepts p.word := by
  rw [hasAcceptedPath_eq_true_iff]
  exact exists_congr fun p => and_congr_right fun _ => A.toFiniteBuchi_accepts p.word
end KILT.FiniteKripke
