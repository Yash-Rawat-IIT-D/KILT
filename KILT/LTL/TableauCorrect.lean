import KILT.LTL.TableauAcceptance
import KILT.Automata.GeneralizedBuchiCorrect

/-!
# Language correctness of the tableau

This module is the semantic correctness bridge for KILT's tableau construction.
For an NNF formula `f`, tableau states are statically consistent assignments to
`f.subformulas`, input symbols are valuations of atomic propositions, and
tableau transitions enforce the literal and temporal `LocalRule`s. Generalized
Büchi acceptance adds the global condition missing from those local rules: an
active strong-until obligation cannot be postponed forever.

The proof establishes both directions of the language correspondence:

* Soundness interprets every formula marked in an arbitrary accepting tableau
  run as true according to `NNF.Sat`. The generalized acceptance sets provide
  the eventual witnesses needed by the strong-until case.
* Completeness uses the proof-only `semanticState` containing exactly the true
  subformulas at each word position. These states form an accepting tableau run
  whenever the root formula holds initially.

Consequently, `accepts_iff_sat` proves that the generalized tableau recognizes
exactly the words satisfying `f`. The final theorem then composes this semantic
result with `FiniteGeneralizedBuchi.toFiniteBuchi_accepts`: the round-robin
counter conversion yields an ordinary CSLib Büchi automaton with the same NNF
language. This is how the LTL semantics, tableau construction, generalized
acceptance obligations, and ordinary executable Büchi backend meet.

The classical truth assignments used for completeness are mathematical
witnesses only; the executable translator enumerates finite tableau states and
does not evaluate `NNF.Sat` on an infinite word.
-/
namespace KILT.LTL.Tableau
open Filter Cslib Cslib.Automata
universe u
variable {AP : Type u} [DecidableEq AP]

/-- Convert generalized acceptance into the semantic witness required by one
pending strong-until claim. If an accepting run marks `a U b` at position `i`,
then some `j ≥ i` marks `b`, while every preceding position from `i` to `j`
marks `a`.

The local tableau rule can carry `a U b` forward while `a` holds. Recurring
membership in this until formula's acceptance set rules out carrying it forever
without `b`. This is the key liveness lemma used by the until case of
`acceptingRun_sound`. -/
theorem until_witness {f a b : NNF AP} {w : Word AP} {ss : ωSequence (State f)}
    (hr : (toGeneralizedBuchi f).AcceptingRun w ss)
    (hg : NNF.until a b ∈ f.subformulas) {i : Nat}
    (hi : (ss i).holds (.until a b)) :
    ∃ j, i ≤ j ∧ (ss j).holds b ∧
      ∀ k, i ≤ k → k < j → (ss k).holds a := by
  classical
  have step k := step_until ((toNA_transition _ _ _).mp (hr.1.trans k)) hg
  have exists_right : ∃ j, i ≤ j ∧ (ss j).holds b := by
    by_contra! h
    have pending : ∀ k ≥ i, (ss k).holds (.until a b) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hi
      | succ k hk ih => exact ((step k).mp ih).resolve_left (h k hk) |>.2
    obtain ⟨j, hij, hj⟩ := frequently_atTop.mp (hr.2 _ (acceptanceSet_mem hg)) i
    exact (mem_acceptanceSet _ |>.mp hj).elim (fun hn => hn (pending j hij)) (h j hij)
  let j := Nat.find exists_right
  have hj : i ≤ j ∧ (ss j).holds b := Nat.find_spec exists_right
  have not_right k (hik : i ≤ k) (hkj : k < j) : ¬ (ss k).holds b := by
    intro hb
    have := Nat.find_min' exists_right ⟨hik, hb⟩
    omega
  have pending : ∀ k ≥ i, k ≤ j → (ss k).holds (.until a b) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact hi
    | succ k hk ih =>
      intro hkj
      exact ((step k).mp (ih (by omega))).resolve_left (not_right k hk (by omega)) |>.2
  refine ⟨j, hj.1, hj.2, fun k hik hkj => ?_⟩
  exact ((step k).mp (pending k hik (by omega))).resolve_left (not_right k hik hkj) |>.1

/-- Soundness of the generalized tableau: every relevant subformula marked by
a state of an accepting run is true under `NNF.Sat` at the corresponding word
position.

Static consistency handles Boolean connectives, transition `LocalRule`s connect
literals and temporal operators to the input valuation and next state, and
`until_witness` supplies the global strong-until witness. This implication is
deliberately one-way for arbitrary tableau states; completeness later builds
special states that mark exactly all semantically true subformulas. -/
theorem acceptingRun_sound {f : NNF AP} {w : Word AP} {ss : ωSequence (State f)}
    (hr : (toGeneralizedBuchi f).AcceptingRun w ss) :
    ∀ g ∈ f.subformulas, ∀ i, (ss i).holds g → NNF.Sat w i g := by
  intro g
  induction g with
  | truth => intro _ _ _; exact NNF.sat_truth.mpr trivial
  | falsehood => intro hg i hi; exact False.elim ((ss i).falsehood hg hi)
  | pos p =>
    intro hg i hi
    exact (step_pos ((toNA_transition _ _ _).mp (hr.1.trans i)) hg).mp hi
  | negAtom p =>
    intro hg i hi
    have hv := (step_negAtom ((toNA_transition _ _ _).mp (hr.1.trans i)) hg).mp hi
    simp [NNF.sat_negAtom, hv]
  | conj a b ha hb =>
    intro hg i hi
    have hc := NNF.subformulas_subset_of_mem hg
    obtain ⟨hia, hib⟩ := (State.conj _ hg).mp hi
    exact (NNF.sat_conj).mpr ⟨ha (hc (by simp [NNF.subformulas])) i hia,
      hb (hc (by simp [NNF.subformulas])) i hib⟩
  | disj a b ha hb =>
    intro hg i hi
    have hc := NNF.subformulas_subset_of_mem hg
    exact ((State.disj _ hg).mp hi).elim
      (fun h => Or.inl (ha (hc (by simp [NNF.subformulas])) i h))
      (fun h => Or.inr (hb (hc (by simp [NNF.subformulas])) i h))
  | next a ha =>
    intro hg i hi
    exact ha (NNF.child_mem_subformulas (by simp [NNF.children]) |>
      NNF.subformulas_subset_of_mem hg) (i+1)
      ((step_next ((toNA_transition _ _ _).mp (hr.1.trans i)) hg).mp hi)
  | «until» a b ha hb =>
    intro hg i hi
    have hc := NNF.subformulas_subset_of_mem hg
    obtain ⟨j, hij, hj, hp⟩ := until_witness hr hg hi
    exact NNF.sat_until.mpr ⟨j, hij, hb (hc (by simp [NNF.subformulas])) j hj,
      fun k hik hkj => ha (hc (by simp [NNF.subformulas])) k (hp k hik hkj)⟩
  | release a b ha hb =>
    intro hg i hi
    have hc := NNF.subformulas_subset_of_mem hg
    have step k := step_release ((toNA_transition _ _ _).mp (hr.1.trans k)) hg
    apply NNF.sat_release.mpr
    intro j hij hleft
    have pending : ∀ k ≥ i, k ≤ j → (ss k).holds (.release a b) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => intro _; exact hi
      | succ k hk ih =>
        intro hkj
        have hrule := (step k).mp (ih (by omega))
        exact hrule.2.resolve_left (fun h => hleft k hk (by omega)
          (ha (hc (by simp [NNF.subformulas])) k h))
    exact hb (hc (by simp [NNF.subformulas])) j ((step j).mp (pending j hij le_rfl)).1

/-- The canonical proof-only tableau state at word position `i`: its assignment
contains exactly those subformulas of `f` that satisfy `NNF.Sat w i`.

The semantic clauses for truth, falsehood, conjunction, and disjunction prove
that this assignment is statically consistent, hence a `State f`. The
definition is noncomputable because satisfaction over an arbitrary infinite
word is used only to witness completeness, not by the executable compiler. -/
noncomputable def semanticState (f : NNF AP) (w : Word AP) (i : Nat) : State f := by
  classical
  let s : Assignment f := Finset.univ.filter fun g => NNF.Sat w i g.val
  have hs (g : NNF AP) (hg : g ∈ f.subformulas) : Holds s g ↔ NNF.Sat w i g := by
    simp [s, Holds, hg]
  refine ⟨s, ?_⟩
  intro ⟨g, hg⟩
  have child {a : NNF AP} (ha : a ∈ g.children) : a ∈ f.subformulas :=
    NNF.subformulas_subset_of_mem hg (NNF.child_mem_subformulas ha)
  cases g with
  | truth => exact (hs _ hg).mpr (NNF.sat_truth.mpr trivial)
  | falsehood => exact fun h => (hs _ hg).mp h
  | conj a b =>
    change Holds s (.conj a b) ↔ Holds s a ∧ Holds s b
    rw [hs _ hg, hs _ (child (by simp [NNF.children])), hs _ (child (by simp [NNF.children]))]
    exact NNF.sat_conj
  | disj a b =>
    change Holds s (.disj a b) ↔ Holds s a ∨ Holds s b
    rw [hs _ hg, hs _ (child (by simp [NNF.children])), hs _ (child (by simp [NNF.children]))]
    exact NNF.sat_disj
  | pos _ | negAtom _ | next _ | «until» _ _ | release _ _ => trivial

/-- The canonical semantic state represents the word exactly: for every
subformula of `f`, syntactic membership in the state is equivalent to semantic
satisfaction at position `i`. This exact correspondence drives both transition
validity and recurring acceptance in the completeness construction. -/
theorem semanticState_represents (f : NNF AP) (w : Word AP) (i : Nat) :
    Represents (semanticState f w i) w i := by
  classical
  intro g hg
  simp [semanticState, State.holds, Holds, hg]

/-- Completeness of the generalized tableau at the run level. If the root NNF
formula is true at position zero, the sequence of exact semantic states is a
valid accepting run over the word.

Root truth gives tableau initiality, adjacent exact representations satisfy all
`LocalRule`s, and each until acceptance set is reached arbitrarily late: an
inactive obligation is accepted immediately, while an active obligation has a
future semantic witness for its right operand. -/
theorem semanticRun_accepting {f : NNF AP} {w : Word AP} (h : NNF.Sat w 0 f) :
    (toGeneralizedBuchi f).AcceptingRun w ⟨fun i => semanticState f w i⟩ := by
  classical
  have hs := semanticState_represents f w
  constructor
  · constructor
    · exact (toNA_start _).mpr ((hs 0 f (NNF.mem_subformulas_self f)).mpr h)
    · intro k
      exact (toNA_transition _ _ _).mpr (step_of_represents (hs k) (hs (k+1)))
  · intro F hF
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hF
    obtain ⟨hg, hu⟩ := mem_untilObligations.mp hg
    obtain ⟨a, b, rfl⟩ := isUntil_iff.mp hu
    apply frequently_atTop.mpr
    intro i
    by_cases hi : NNF.Sat w i (.until a b)
    · obtain ⟨j, hij, hj, _⟩ := NNF.sat_until.mp hi
      refine ⟨j, hij, mem_acceptanceSet _ |>.mpr (Or.inr ?_)⟩
      exact (hs j b (NNF.subformulas_subset_of_mem hg (by simp [NNF.subformulas]))).mpr hj
    · exact ⟨i, le_rfl, mem_acceptanceSet _ |>.mpr
        (Or.inl (fun hh => hi ((hs i _ hg).mp hh)))⟩
/-- The central tableau language-correctness theorem. The generalized tableau
accepts an infinite valuation word exactly when that word satisfies the root NNF
formula at position zero.

The forward direction applies `acceptingRun_sound` to the root formula marked
by an initial state. The reverse direction supplies the accepting sequence of
exact semantic states from `semanticRun_accepting`. -/
theorem accepts_iff_sat (f : NNF AP) (w : Word AP) :
    (toGeneralizedBuchi f).Accepts w ↔ NNF.Sat w 0 f := by
  constructor
  · rintro ⟨ss, hr⟩
    exact acceptingRun_sound hr f (NNF.mem_subformulas_self f) 0
      ((toNA_start _).mp hr.1.start)
  · intro h
    exact ⟨_, semanticRun_accepting h⟩

/-- End-to-end automata correspondence for an NNF formula: the ordinary finite
Büchi automaton obtained by adding the verified round-robin counter accepts
exactly the infinite valuation words satisfying `f`.

This composes `accepts_iff_sat` with the generic language-preservation theorem
from `GeneralizedBuchiCorrect`. It is the boundary used by later compilation
and model-checking proofs: tableau-specific generalized obligations have become
ordinary CSLib Büchi acceptance without changing the declared NNF semantics. -/
theorem toFiniteBuchi_accepts (f : NNF AP) (w : Word AP) :
    ωAcceptor.Accepts (toGeneralizedBuchi f).toFiniteBuchi.toCSLib w ↔ NNF.Sat w 0 f := by
  rw [Automata.FiniteGeneralizedBuchi.toFiniteBuchi_accepts, accepts_iff_sat]

end KILT.LTL.Tableau
