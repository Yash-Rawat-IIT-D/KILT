import KILT
import Examples.Tableau

/-!
# Tableau and compiled word languages

Finite assertions below are kernel checked. Infinite-word claims use the
general language theorem and explicit semantic witnesses. The final #eval
displays execute finite construction only; they are not proofs of acceptance.
-/
namespace Examples.Translation
open KILT.LTL KILT.LTL.Tableau Cslib Cslib.Automata
open scoped KILT.LTL

def p : NNF Nat := .pos 0
def q : NNF Nat := .pos 1
def fp : Formula Nat := .atom 0
def fq : Formula Nat := .atom 1
def off : Valuation Nat := fun _ => false
def onlyP : Valuation Nat := fun a => a == 0
def onlyQ : Valuation Nat := fun a => a == 1
def both : Valuation Nat := fun a => a == 0 || a == 1
def constant (v : Valuation Nat) : Word Nat := ωSequence.const v

def u : NNF Nat := .until p q
def v : NNF Nat := .until q p
def nested : NNF Nat := .until u v

/-- Root first; the repeated left-child obligation keeps its first position. -/
theorem obligation_order : untilObligations (.conj nested u) = [nested, u, v] := by decide
example : (untilObligations (.conj u u)).length = 1 := by decide
example : untilObligations (.release p q) = [] := by decide
example : untilObligations (.next (.conj p q)) = [] := by decide
example : (toGeneralizedBuchi u).accepting.length = 1 := by decide
example : (toGeneralizedBuchi (.conj u v)).accepting.length = 2 := by decide
example : Examples.Tableau.waiting ∉ acceptanceSet Examples.Tableau.u Examples.Tableau.u := by decide
example : Examples.Tableau.fulfilled ∈ acceptanceSet Examples.Tableau.u Examples.Tableau.u := by decide
example : Examples.Tableau.emptyUntil ∈ acceptanceSet Examples.Tableau.u Examples.Tableau.u := by decide

/-- The existing infinite local run cannot pass the new acceptance condition. -/
theorem postponed_run_rejected :
    ¬ (toGeneralizedBuchi Examples.Tableau.u).AcceptingRun
      ⟨fun _ => Examples.Tableau.onlyP⟩ ⟨fun _ => Examples.Tableau.waiting⟩ := by
  intro hr
  exact Examples.Tableau.postponed_word_fails
    (acceptingRun_sound hr _ (NNF.mem_subformulas_self _) 0 (by decide))

theorem postponed_word_rejected :
    ¬ (toGeneralizedBuchi Examples.Tableau.u).Accepts ⟨fun _ => Examples.Tableau.onlyP⟩ := by
  rw [accepts_iff_sat]
  exact Examples.Tableau.postponed_word_fails

example : (toGeneralizedBuchi (.truth : NNF Nat)).Accepts (constant off) :=
  (accepts_iff_sat _ _).mpr (NNF.sat_truth.mpr trivial)
example : ¬ (toGeneralizedBuchi (.falsehood : NNF Nat)).Accepts (constant both) := by
  rw [accepts_iff_sat]; exact id
example : (toGeneralizedBuchi p).Accepts (constant onlyP) :=
  (accepts_iff_sat _ _).mpr rfl
example : (toGeneralizedBuchi (.negAtom 0 : NNF Nat)).Accepts (constant off) := by
  rw [accepts_iff_sat, NNF.sat_negAtom]; decide
example : ¬ (toGeneralizedBuchi (.conj p (.negAtom 0))).Accepts (constant onlyP) := by
  rw [accepts_iff_sat, NNF.sat_conj]
  exact fun h => h.2 h.1
example : (toGeneralizedBuchi (.disj p q)).Accepts (constant onlyQ) :=
  (accepts_iff_sat _ _).mpr (Or.inr rfl)
example : (toGeneralizedBuchi (.conj p q)).Accepts (constant both) :=
  (accepts_iff_sat _ _).mpr ((NNF.sat_conj).mpr ⟨rfl, rfl⟩)

/-- Immediate fulfillment needs no left operand, even when it is falsehood. -/
theorem until_now :
    (toGeneralizedBuchi (.until .falsehood q)).Accepts (constant onlyQ) := by
  apply (accepts_iff_sat _ _).mpr
  exact ⟨0, le_rfl, rfl, fun _ _ hk => (Nat.not_lt_zero _ hk).elim⟩

def delayed : Word Nat := ⟨fun i => if i < 2 then onlyP else onlyQ⟩

theorem until_delayed : (toGeneralizedBuchi u).Accepts delayed := by
  apply (accepts_iff_sat _ _).mpr
  refine ⟨2, by decide, rfl, ?_⟩
  intro k _ hk
  change (if k < 2 then onlyP else onlyQ) 0 = true
  simp [hk, onlyP]

theorem release_forever :
    (toGeneralizedBuchi (.release p q)).Accepts (constant onlyQ) := by
  apply (accepts_iff_sat _ _).mpr
  exact NNF.sat_release.mpr (fun _ _ _ => rfl)

/-- A left operand at zero cannot excuse a false right operand at zero. -/
theorem release_endpoint :
    ¬ (toGeneralizedBuchi (.release p q)).Accepts (constant onlyP) := by
  rw [accepts_iff_sat]
  intro h
  have hh := NNF.sat_release.mp h 0 le_rfl (fun _ _ hk => (Nat.not_lt_zero _ hk).elim)
  change false = true at hh
  contradiction

/-- Absence need not mean falsity, even along an accepting run. -/
def optionalRelease : NNF Nat := .disj (.release p q) .truth
def partialReleaseState : State optionalRelease :=
  Examples.Tableau.state optionalRelease {optionalRelease, .truth, q} (by decide)

theorem partial_release_accepting :
    (toGeneralizedBuchi optionalRelease).AcceptingRun (constant onlyQ)
      (ωSequence.const partialReleaseState) := by
  constructor
  · constructor
    · exact (toNA_start _).mpr (by decide)
    · intro _
      apply (toNA_transition _ _ _).mpr
      change Step partialReleaseState partialReleaseState onlyQ
      decide
  · intro F hF
    have : (toGeneralizedBuchi optionalRelease).accepting = [] := by decide
    simp [this] at hF

theorem partial_release_not_represents :
    ¬ Represents partialReleaseState (constant onlyQ) 0 := by
  intro h
  have hr := (h (.release p q) (by decide)).mpr
    (NNF.sat_release.mpr (fun _ _ _ => rfl))
  exact (by decide : ¬ partialReleaseState.holds (.release p q)) hr

theorem two_obligations :
    (toGeneralizedBuchi (.conj u v)).Accepts (constant both) := by
  apply (accepts_iff_sat _ _).mpr
  apply NNF.sat_conj.mpr
  constructor <;> exact ⟨0, le_rfl, rfl, fun _ _ hk => (Nat.not_lt_zero _ hk).elim⟩

theorem only_one_obligation :
    ¬ (toGeneralizedBuchi (.conj (.until .truth p) (.until .truth q))).Accepts
      (constant onlyP) := by
  rw [accepts_iff_sat, NNF.sat_conj]
  rintro ⟨_, j, _, hj, _⟩
  change false = true at hj
  contradiction

example : (toGeneralizedBuchi nested).Accepts (constant both) := by
  apply (accepts_iff_sat _ _).mpr
  refine ⟨0, le_rfl, ?_, fun _ _ hk => (Nat.not_lt_zero _ hk).elim⟩
  exact ⟨0, le_rfl, rfl, fun _ _ hk => (Nat.not_lt_zero _ hk).elim⟩
example : (toGeneralizedBuchi (.conj u u)).Accepts delayed := by
  rw [accepts_iff_sat, NNF.sat_conj]
  have h := (accepts_iff_sat u delayed).mp until_delayed
  exact ⟨h, h⟩

def switchWord : Word Nat := ⟨fun i => if i = 0 then onlyP else onlyQ⟩
example : ωAcceptor.Accepts (𝒩 fq).toBuchi.toBuchi switchWord :=
  ((𝒩 fq).toBuchi_accepts switchWord).mpr rfl
example : ¬ ωAcceptor.Accepts (𝒩 fp).toBuchi.toBuchi switchWord := by
  rw [Formula.toBuchi_accepts]
  change ¬ (false = true)
  decide

/-- Only position zero makes q true: compilation must consume that valuation. -/
def pulse : Word Nat := ⟨fun i => if i = 0 then onlyQ else off⟩
theorem eventually_at_zero : ωAcceptor.Accepts (◇ fq).toBuchi.toBuchi pulse := by
  apply ((◇ fq).toBuchi_accepts pulse).mpr
  exact sat_eventually.mpr ⟨0, le_rfl, rfl⟩

example : ωAcceptor.Accepts (□ fq).toBuchi.toBuchi (constant onlyQ) := by
  rw [Formula.toBuchi_accepts]
  exact sat_globally.mpr (fun _ _ => rfl)
example : ωAcceptor.Accepts (fp ⟹ ◇ fq).toBuchi.toBuchi (constant onlyQ) := by
  rw [Formula.toBuchi_accepts]
  apply sat_imp.mpr
  intro hp
  change false = true at hp
  contradiction
example : ωAcceptor.Accepts (Formula.release fp fq).toBuchi.toBuchi (constant onlyQ) := by
  rw [Formula.toBuchi_accepts]
  exact sat_release.mpr (fun _ _ _ => rfl)
example : ωAcceptor.Accepts (¬ₗ (¬ₗ fq)).toBuchi.toBuchi (constant onlyQ) := by
  rw [Formula.toBuchi_accepts]
  exact fun h => h rfl
example : ωAcceptor.Accepts (¬ₗ (fp 𝒰 fq)).toBuchi.toBuchi (constant off) := by
  rw [Formula.toBuchi_accepts]
  rintro ⟨j, _, hj, _⟩
  change false = true at hj
  contradiction
example : ωAcceptor.Accepts (¬ₗ (Formula.release fp fq)).toBuchi.toBuchi (constant off) := by
  rw [Formula.toBuchi_accepts]
  intro h
  have hh := sat_release.mp h 0 le_rfl (fun _ _ hk => (Nat.not_lt_zero _ hk).elim)
  change false = true at hh
  contradiction

/-- Independent handwritten language proofs remain comparison oracles. -/
theorem agrees_eventually (w : Word Nat) :
    ωAcceptor.Accepts (◇ fq).toBuchi.toBuchi w ↔
      ωAcceptor.Accepts (KILT.Automata.Monitors.eventually 1).toBuchi w := by
  rw [Formula.toBuchi_accepts, KILT.Automata.Monitors.eventually_accepts]
  rfl
theorem agrees_notEventually (w : Word Nat) :
    ωAcceptor.Accepts (¬ₗ (◇ fq)).toBuchi.toBuchi w ↔
      ωAcceptor.Accepts (KILT.Automata.Monitors.notEventually 1).toBuchi w := by
  rw [Formula.toBuchi_accepts, KILT.Automata.Monitors.notEventually_accepts]
  rfl
theorem agrees_notResponse (w : Word Nat) :
    ωAcceptor.Accepts (¬ₗ (□ (fp ⟹ ◇ fq))).toBuchi.toBuchi w ↔
      ωAcceptor.Accepts (KILT.Automata.Monitors.notResponse 0 1).toBuchi w := by
  rw [Formula.toBuchi_accepts, KILT.Automata.Monitors.notResponse_accepts]
  rfl

/-- Compiled construction counts: (closure, until obligations, converted carrier). -/
def constructionCounts (φ : Formula Nat) : Nat × Nat × Nat :=
  (φ.normalize.subformulas.card, (untilObligations φ.normalize).length,
    Fintype.card (Formula.AutomatonState φ))
example : Fintype.card (Formula.AutomatonState (◇ fq)) = 4 := by decide
example : Fintype.card (Formula.AutomatonState (Formula.truth : Formula Nat)) = 1 := by decide
example : (◇ fq).toBuchi.initials.card = 2 := by decide
example : (◇ fq).toBuchi.accepting.card = 3 := by decide
#eval constructionCounts (Formula.truth : Formula Nat)
#eval constructionCounts (◇ fq)
#eval constructionCounts (𝒩 fp)
#eval constructionCounts (Formula.release fp fq)
#eval ((◇ fq).toBuchi.initials.card, (◇ fq).toBuchi.accepting.card)
end Examples.Translation
