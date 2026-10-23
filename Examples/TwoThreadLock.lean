import KILT

/-!
# Two threads and a shared lock

Assumptions: one thread takes one logical instruction per global transition;
reads/writes observe a single shared lock bit (sequential consistency). There
is no fairness: either thread may be ignored forever. A blocked test spins.
Idle threads request when scheduled; critical threads release when scheduled.
These are finite protocol models, not a claim about a particular CPU or mutex.

Broken: Idle → Trying → Checked → Critical → Idle. Trying reads the lock;
Checked remembers a successful test and later writes, without checking again.
Atomic: Idle → Trying → Critical → Idle, combining test and claim. Checked
remains in the common carrier for comparison but is unreachable atomically.

The model separates instructions, scheduler, labels and LTL properties so a
turn variable, alternative scheduler or Peterson protocol can be added later.
Uses KILT's current semantics (informed by LeanLTL) and verified monitors;
it does not depend on LeanLTL or the unfinished general formula translator.
-/
namespace Examples.TwoThreadLock
open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL

inductive Thread where | zero | one deriving DecidableEq, Repr
inductive PC where | idle | trying | checked | critical deriving DecidableEq, Repr
inductive Mode where | broken | atomic deriving DecidableEq, Repr
instance : Fintype PC where
  elems := {.idle, .trying, .checked, .critical}
  complete p := by cases p <;> simp

structure State where
  pc0 : PC
  pc1 : PC
  locked : Bool
  deriving DecidableEq, Repr

instance : Fintype State := Fintype.ofEquiv (PC × PC × Bool)
  { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
    invFun := fun s => (s.pc0, s.pc1, s.locked)
    left_inv := by intro p; rfl
    right_inv := by intro s; rfl }

inductive Atom where
  | requesting (thread : Thread)
  | inCritical (thread : Thread)
  | lockHeld
  deriving DecidableEq, Repr

def pc (s : State) : Thread → PC | .zero => s.pc0 | .one => s.pc1

def label (s : State) : Valuation Atom
  | .requesting t => pc s t == .trying || pc s t == .checked
  | .inCritical t => pc s t == .critical
  | .lockHeld => s.locked

/-- A failed test spins; successful broken tests retain permission in Checked. -/
def instruction (mode : Mode) (p : PC) (locked : Bool) : PC × Bool :=
  match p with
  | .idle => (.trying, locked)
  | .trying => if locked then (.trying, locked)
      else if mode = .broken then (.checked, locked) else (.critical, true)
  | .checked => (.critical, true)
  | .critical => (.idle, false)

def advance (mode : Mode) (thread : Thread) (s : State) : State :=
  let result := instruction mode (pc s thread) s.locked
  match thread with
  | .zero => { s with pc0 := result.1, locked := result.2 }
  | .one => { s with pc1 := result.1, locked := result.2 }

@[simp] theorem advance_zero_preserves_pc1 (m : Mode) (s : State) :
    (advance m .zero s).pc1 = s.pc1 := rfl
@[simp] theorem advance_one_preserves_pc0 (m : Mode) (s : State) :
    (advance m .one s).pc0 = s.pc0 := rfl

def initial : State := ⟨.idle, .idle, false⟩
def model (mode : Mode) : FiniteKripke State Atom where
  initials := {initial}
  initials_nonempty := by simp
  successors s := {advance mode .zero s, advance mode .one s}
  label := label
abbrev broken := model .broken
abbrev atomic := model .atomic

theorem serial (mode : Mode) : (model mode).toKripke.Serial := by
  intro s
  exact ⟨advance mode .zero s, by change _ ∈ ({_, _} : Finset State); simp⟩

example : broken.isSerial = true := broken.isSerial_eq_true_iff.mpr (serial .broken)
example : atomic.isSerial = true := atomic.isSerial_eq_true_iff.mpr (serial .atomic)
/-- A failed test is an explicit busy-wait step, not an automatically inserted loop. -/
example : advance .atomic .zero ⟨.trying, .critical, true⟩ = ⟨.trying, .critical, true⟩ := by decide
example : advance .atomic .zero ⟨.trying, .idle, false⟩ = ⟨.critical, .idle, true⟩ := by decide
example : advance .broken .zero ⟨.trying, .idle, false⟩ = ⟨.checked, .idle, false⟩ := by decide
example : advance .atomic .zero ⟨.critical, .trying, true⟩ = ⟨.idle, .trying, false⟩ := by decide

/-- Schedules are infinite choices; no finite-prefix witness is called a lasso output. -/
def execution (mode : Mode) (schedule : Nat → Thread) : Nat → State
  | 0 => initial
  | n+1 => advance mode (schedule n) (execution mode schedule n)

def scheduledPath (mode : Mode) (schedule : Nat → Thread) : (model mode).toKripke.Path where
  states := ⟨execution mode schedule⟩
  valid n := by
    change advance mode (schedule n) _ ∈ ({_, _} : Finset State)
    cases schedule n <;> simp

theorem scheduledPath_initial (mode : Mode) (schedule : Nat → Thread) :
    (scheduledPath mode schedule).IsInitial := by change initial ∈ ({initial} : Finset State); simp

def critical (t : Thread) : Formula Atom := .atom (.inCritical t)
def request (t : Thread) : Formula Atom := .atom (.requesting t)
def mutualExclusion : Formula Atom := □ (¬ₗ (critical .zero ∧ₗ critical .one))
def starvationFreedom (t : Thread) : Formula Atom := □ (request t ⟹ ◇ critical t)
def bothCritical (s : State) : Prop := s.pc0 = .critical ∧ s.pc1 = .critical

instance (s : State) : Decidable (bothCritical s) :=
  inferInstanceAs (Decidable (s.pc0 = .critical ∧ s.pc1 = .critical))

/-- A finite interleaving exposes the race, followed by an infinite schedule. -/
def raceSchedule (n : Nat) : Thread :=
  ([.zero, .zero, .one, .one, .zero, .one] : List Thread)[n]?.getD .zero

def racePath := scheduledPath .broken raceSchedule
example : (racePath.states 2) = ⟨.checked, .idle, false⟩ := by decide
example : (racePath.states 4) = ⟨.checked, .checked, false⟩ := by decide
theorem race_collision : bothCritical (racePath.states 6) := by decide

theorem broken_not_mutualExclusion : ¬ broken.toKripke.Satisfies mutualExclusion := by
  intro h
  have hall := sat_globally.mp (h racePath (scheduledPath_initial _ _))
  have hbad := hall 6 (by omega)
  apply hbad
  rw [sat_conj]
  change label (racePath.states 6) (.inCritical .zero) = true ∧
    label (racePath.states 6) (.inCritical .one) = true
  constructor <;> decide

/-- Preserve the lock ownership facts without restricting the common state type. -/
def AtomicInvariant (s : State) : Prop :=
  s.pc0 ≠ .checked ∧ s.pc1 ≠ .checked ∧
  (s.pc0 = .critical → s.locked = true) ∧
  (s.pc1 = .critical → s.locked = true) ∧ ¬ bothCritical s

theorem atomic_step_invariant (s : State) (hi : AtomicInvariant s)
    (t : State) (ht : t ∈ atomic.successors s) : AtomicInvariant t := by
  rcases s with ⟨p0, p1, locked⟩
  simp only [model, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;>
    cases p0 <;> cases p1 <;> cases locked <;>
    simp_all [AtomicInvariant, bothCritical, advance, instruction, pc]

theorem atomic_path_invariant (path : atomic.toKripke.Path) (hi : path.IsInitial) :
    ∀ i, AtomicInvariant (path.states i) := by
  intro i
  induction i with
  | zero =>
    have hs : path.states 0 = initial := by
      change path.states 0 ∈ ({initial} : Finset State) at hi
      simpa using hi
    rw [hs]
    simp [AtomicInvariant, initial, bothCritical]
  | succ i ih => exact atomic_step_invariant _ ih _ (path.valid i)

theorem atomic_mutualExclusion : atomic.toKripke.Satisfies mutualExclusion := by
  intro path hi
  apply sat_globally.mpr
  intro i _
  have hs := (atomic_path_invariant path hi i).2.2.2.2
  rw [sat_neg, sat_conj]
  change ¬ (label (path.states i) (.inCritical .zero) = true ∧
    label (path.states i) (.inCritical .one) = true)
  simpa [bothCritical, label, pc] using hs

/-- Thread zero requests once; thread one then repeatedly acquires/releases. -/
def unfairSchedule (n : Nat) : Thread := if n = 0 then .zero else .one
def unfairPath := scheduledPath .atomic unfairSchedule

theorem unfair_waits : ∀ n, (unfairPath.states (n+1)).pc0 = .trying := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (advance .atomic (unfairSchedule (n+1)) _).pc0 = .trying
    change (execution .atomic unfairSchedule (n+1)).pc0 = .trying at ih
    simpa [unfairSchedule, advance] using ih

theorem unfair_not_response : ¬ WordSat unfairPath.word (starvationFreedom .zero) := by
  intro h
  have hr := (sat_globally.mp h) 1 (by omega)
  have hreq : Sat unfairPath.word 1 (request .zero) := by
    change label (unfairPath.states 1) (.requesting .zero) = true
    decide
  obtain ⟨j, hj, hc⟩ := sat_eventually.mp ((sat_imp.mp hr) hreq)
  obtain ⟨n, rfl⟩ : ∃ n, j = n+1 := ⟨j-1, by omega⟩
  change label (unfairPath.states (n+1)) (.inCritical .zero) = true at hc
  simp [label, pc, unfair_waits n] at hc

theorem atomic_not_starvationFree : ¬ atomic.toKripke.Satisfies (starvationFreedom .zero) :=
  fun h => unfair_not_response (h unfairPath (scheduledPath_initial _ _))

-- The response monitors are supplied by hand, with existing language proofs.
-- General formula-input checking is still a separate compiler milestone.
/-- Prove the verdict via checker correctness and the semantic counterexample;
`#eval` below separately executes the Boolean search without a native proof axiom. -/
theorem atomic_response_check :
    atomic.checkAgainst (Monitors.notResponse (.requesting .zero) (.inCritical .zero))
      (serial .atomic) = false := by
  cases hc : atomic.checkAgainst (Monitors.notResponse (.requesting .zero) (.inCritical .zero))
      (serial .atomic) with
  | false => rfl
  | true =>
    exact False.elim (atomic_not_starvationFree
      ((atomic.checkAgainst_correct _ (serial .atomic) _
        (Monitors.notResponse_accepts (Atom.requesting .zero) (Atom.inCritical .zero))).mp hc))

theorem atomic_not_starvationFree_from_checker :
    ¬ atomic.toKripke.Satisfies (starvationFreedom .zero) := by
  intro h
  have hc := (atomic.checkAgainst_correct _ (serial .atomic) _
    (Monitors.notResponse_accepts (Atom.requesting .zero) (Atom.inCritical .zero))).mpr h
  rw [atomic_response_check] at hc
  cases hc

#eval (List.range 7).map (fun n => racePath.states n)
#eval (List.range 9).map (fun n => unfairPath.states n)
#eval Fintype.card State
#eval (broken.reachableSet.card, atomic.reachableSet.card)
#eval atomic.checkAgainst (Monitors.notResponse (Atom.requesting .zero) (Atom.inCritical .zero))
  (serial .atomic)
end Examples.TwoThreadLock
