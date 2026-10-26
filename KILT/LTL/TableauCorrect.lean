import KILT.LTL.TableauAcceptance
import KILT.Automata.GeneralizedBuchiCorrect

/-!
# Language correctness of the tableau

Soundness concerns present obligations only. Completeness uses classical truth
assignments as mathematical witnesses, never as executable translator data.
-/
namespace KILT.LTL.Tableau
open Filter Cslib Cslib.Automata
universe u
variable {AP : Type u} [DecidableEq AP]

/-- A pending until must eventually reach its right operand on an accepting run. -/
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

/-- Every present subformula is true, at every position of an accepting run. -/
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

/-- Proof-only state consisting of precisely the true subformulas. -/
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

theorem semanticState_represents (f : NNF AP) (w : Word AP) (i : Nat) :
    Represents (semanticState f w i) w i := by
  classical
  intro g hg
  simp [semanticState, State.holds, Holds, hg]

/-- The exact-truth sequence is accepting whenever the root holds initially. -/
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
/-- The generalized tableau accepts exactly the satisfying infinite words. -/
theorem accepts_iff_sat (f : NNF AP) (w : Word AP) :
    (toGeneralizedBuchi f).Accepts w ↔ NNF.Sat w 0 f := by
  constructor
  · rintro ⟨ss, hr⟩
    exact acceptingRun_sound hr f (NNF.mem_subformulas_self f) 0
      ((toNA_start _).mp hr.1.start)
  · intro h
    exact ⟨_, semanticRun_accepting h⟩

theorem toFiniteBuchi_accepts (f : NNF AP) (w : Word AP) :
    ωAcceptor.Accepts (toGeneralizedBuchi f).toFiniteBuchi.toCSLib w ↔ NNF.Sat w 0 f := by
  rw [Automata.FiniteGeneralizedBuchi.toFiniteBuchi_accepts, accepts_iff_sat]

end KILT.LTL.Tableau
