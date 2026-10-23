import KILT.Automata.FiniteBuchi
import KILT.LTL.Basic

/-!
# Small automata with proved temporal languages

These handwritten constructions validate the backend before general LTL
translation. Waiting is nonaccepting; committing is accepting. A commitment
consumes its triggering symbol, so the maintained obligation starts next.
-/
namespace KILT.Automata.Monitors
open Cslib Cslib.Automata Filter KILT.LTL
universe u v
variable {Symbol : Type u} {AP : Type v}

/-- Guess a triggering position, then maintain an obligation forever. -/
def guessAndStay (trigger maintain : Symbol → Bool) : FiniteBuchi Bool Symbol where
  initials := {false}
  successors seen symbol :=
    if seen then (if maintain symbol then {true} else ∅)
    else (if trigger symbol then {false, true} else {false})
  accepting := {true}

@[simp] theorem guess_wait_false (trigger maintain : Symbol → Bool) (symbol : Symbol) :
    false ∈ (guessAndStay trigger maintain).successors false symbol := by
  cases h : trigger symbol <;> simp [guessAndStay, h]

@[simp] theorem guess_wait_true (trigger maintain : Symbol → Bool) (symbol : Symbol) :
    true ∈ (guessAndStay trigger maintain).successors false symbol ↔ trigger symbol = true := by
  cases h : trigger symbol <;> simp [guessAndStay, h]

@[simp] theorem guess_seen (trigger maintain : Symbol → Bool) (symbol : Symbol) (next : Bool) :
    next ∈ (guessAndStay trigger maintain).successors true symbol ↔
      maintain symbol = true ∧ next = true := by
  cases next <;> cases h : maintain symbol <;> simp [guessAndStay, h]

theorem guessAndStay_accepts (trigger maintain : Symbol → Bool) (word : ωSequence Symbol) :
    ωAcceptor.Accepts (guessAndStay trigger maintain).toBuchi word ↔
      ∃ j, trigger (word j) = true ∧ ∀ k, j < k → maintain (word k) = true := by
  constructor
  · rintro ⟨ss, run, hacc⟩
    have hstart : ss 0 = false := by
      have h := run.start
      change ss 0 ∈ ({false} : Finset Bool) at h
      simpa using h
    have step (i : Nat) : ss (i + 1) ∈
        (guessAndStay trigger maintain).successors (ss i) (word i) := run.trans i
    have entered : ∀ n, ss n = true → ∃ j < n, ss j = false ∧ ss (j + 1) = true := by
      intro n
      induction n with
      | zero => simp [hstart]
      | succ n ih =>
        intro hn
        cases hprev : ss n with
        | false => exact ⟨n, by omega, hprev, hn⟩
        | true =>
          rcases ih hprev with ⟨j, hj, hwait, hseen⟩
          exact ⟨j, by omega, hwait, hseen⟩
    obtain ⟨n, _, hn⟩ := frequently_atTop.mp hacc 0
    have hn' : ss n = true := by
      change ss n ∈ ({true} : Finset Bool) at hn
      simpa using hn
    obtain ⟨j, _, hjwait, hjseen⟩ := entered n hn'
    have htrigger : trigger (word j) = true := by
      have h := step j
      rw [hjwait, hjseen] at h
      exact (guess_wait_true trigger maintain (word j)).mp h
    have seen_step (i : Nat) (hi : ss i = true) :
        maintain (word i) = true ∧ ss (i + 1) = true := by
      have h := step i
      rw [hi] at h
      exact (guess_seen trigger maintain (word i) _).mp h
    have stays (k : Nat) (hk : j < k) : ss k = true := by
      have hle : j + 1 ≤ k := by omega
      induction k, hle using Nat.le_induction with
      | base => exact hjseen
      | succ k _ ih => exact (seen_step k (ih (by omega))).2
    exact ⟨j, htrigger, fun k hk => (seen_step k (stays k hk)).1⟩
  · rintro ⟨j, htrigger, hmaintain⟩
    let ss : ωSequence Bool := fun n => decide (j < n)
    refine ⟨ss, ⟨?_, ?_⟩, frequently_atTop.mpr ?_⟩
    · change decide (j < 0) ∈ ({false} : Finset Bool)
      simp
    · intro i
      change decide (j < i + 1) ∈
        (guessAndStay trigger maintain).successors (decide (j < i)) (word i)
      by_cases hi : j < i
      · have hnext : j < i + 1 := by omega
        simp only [hi, hnext, decide_true]
        exact (guess_seen trigger maintain (word i) true).mpr ⟨hmaintain i hi, rfl⟩
      · by_cases he : i = j
        · subst i
          simp [htrigger]
        · have hnext : ¬j < i + 1 := by omega
          simp [hi, hnext]
    · intro n
      refine ⟨max n (j + 1), le_max_left _ _, ?_⟩
      have hlt : j < max n (j + 1) := by omega
      change decide (j < max n (j + 1)) ∈ ({true} : Finset Bool)
      simp [hlt]

/-- Nondeterministically guess an occurrence of the named atom. -/
def eventually (q : AP) : FiniteBuchi Bool (Valuation AP) :=
  guessAndStay (fun valuation => valuation q) (fun _ => true)

theorem eventually_accepts (q : AP) (word : Word AP) :
    ωAcceptor.Accepts (eventually q).toBuchi word ↔ WordSat word (Formula.eventually (.atom q)) := by
  rw [eventually, guessAndStay_accepts]
  simp [WordSat, sat_eventually, sat_atom]

/-- Accept exactly words on which the named atom never holds. -/
def notEventually (q : AP) : FiniteBuchi Unit (Valuation AP) where
  initials := {()}
  successors _ valuation := if valuation q then ∅ else {()}
  accepting := {()}

theorem notEventually_accepts (q : AP) (word : Word AP) :
    ωAcceptor.Accepts (notEventually q).toBuchi word ↔
      ¬ WordSat word (Formula.eventually (.atom q)) := by
  constructor
  · rintro ⟨ss, run, _⟩ hevent
    rcases sat_eventually.mp hevent with ⟨j, _, hj⟩
    have h := run.trans j
    change ss (j + 1) ∈ (if word j q then (∅ : Finset Unit) else {()}) at h
    change word j q = true at hj
    simp [hj] at h
  · intro hnever
    have hfalse (i : Nat) : word i q = false := by
      cases h : word i q with
      | false => rfl
      | true => exact False.elim (hnever (sat_eventually.mpr ⟨i, Nat.zero_le _, h⟩))
    refine ⟨ωSequence.const (), ⟨by change () ∈ ({()} : Finset Unit); simp, ?_⟩, ?_⟩
    · intro i
      simp [notEventually, FiniteBuchi.toBuchi, hfalse]
    · exact frequently_atTop.mpr fun n => ⟨n, le_rfl, by change () ∈ ({()} : Finset Unit); simp⟩

/-- Guess an unanswered request, then require grant to remain false. -/
def notResponse (p q : AP) : FiniteBuchi Bool (Valuation AP) :=
  guessAndStay (fun valuation => valuation p && !valuation q) (fun valuation => !valuation q)

theorem notResponse_accepts (p q : AP) (word : Word AP) :
    ωAcceptor.Accepts (notResponse p q).toBuchi word ↔
      ¬ WordSat word (Formula.globally (Formula.imp (.atom p) (Formula.eventually (.atom q)))) := by
  classical
  rw [notResponse, guessAndStay_accepts]
  simp only [Bool.and_eq_true, Bool.not_eq_true', WordSat, sat_globally, sat_imp,
    sat_atom, sat_eventually]
  constructor
  · rintro ⟨j, ⟨hp, hq⟩, htail⟩ hall
    obtain ⟨k, hjk, hk⟩ := hall j (Nat.zero_le _) hp
    by_cases heq : k = j
    · subst k; simp [hq] at hk
    · have : j < k := by omega
      have := htail k this
      simp [this] at hk
  · intro hnot
    push Not at hnot
    rcases hnot with ⟨j, _, hp, hq⟩
    have hfalse (k : Nat) (hk : j ≤ k) : word k q = false := by
      cases h : word k q with
      | false => rfl
      | true => exact False.elim (hq k hk h)
    exact ⟨j, ⟨hp, hfalse j le_rfl⟩, fun k hk => hfalse k (by omega)⟩

end KILT.Automata.Monitors
