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

Read the example as model data → instruction choices → labels and properties
→ a racing execution → an atomic invariant → an unfair execution. The two
executions explain different failures: a finite safety violation and an
infinite unmet request. The final `checkAgainst` call shows how to supply a
violation monitor and connect its verdict to the semantic property. For the
shorter formula-input frontend, see `Examples/Demos/Frontend.lean`; extracted
monitor witnesses are illustrated in `Examples/Regression/Counterexample.lean`.
-/
namespace Examples.TwoThreadLock
open KILT KILT.LTL KILT.Automata
open scoped KILT.LTL

/-! ## Model data: two program counters and one shared lock bit -/

/-- Identify which thread is observed or scheduled. Deriving equality lets Lean
compare thread names; `Repr` makes the printed executions readable. -/
inductive Thread where | zero | one deriving DecidableEq, Repr
/-- The instruction positions. `checked` remembers a successful lock test;
retaining it before a separate claim is what permits the broken race. -/
inductive PC where | idle | trying | checked | critical deriving DecidableEq, Repr
/-- Choose split test/claim or atomic test-and-claim while sharing the state type. -/
inductive Mode where | broken | atomic deriving DecidableEq, Repr
/-- Enumerate instruction positions so Lean can enumerate finite global states. -/
instance : Fintype PC where
  elems := {.idle, .trying, .checked, .critical}
  complete p := by cases p <;> simp

/-- A complete snapshot records both threads and the shared bit, so advancing
one thread can still observe changes made by the other. -/
structure State where
  /-- The next instruction position of thread zero. -/
  pc0 : PC
  /-- The next instruction position of thread one. -/
  pc1 : PC
  /-- The shared lock bit; ownership facts are established by the invariant below. -/
  locked : Bool
  deriving DecidableEq, Repr

/-- Reuse finite product enumeration instead of listing every snapshot by hand.
This includes unreachable combinations; model transitions determine reachability. -/
instance : Fintype State := Fintype.ofEquiv (PC × PC × Bool)
  { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
    invFun := fun s => (s.pc0, s.pc1, s.locked)
    left_inv := by intro p; rfl
    right_inv := by intro s; rfl }

/-- The observations available to formulas: a chosen thread's pending request
or critical-section status, and the shared lock bit. -/
inductive Atom where
  | requesting (thread : Thread)
  | inCritical (thread : Thread)
  | lockHeld
  deriving DecidableEq, Repr

/-- Select a thread's counter uniformly, so labels and instructions need not
duplicate the thread-zero/thread-one case split. -/
def pc (s : State) : Thread → PC | .zero => s.pc0 | .one => s.pc1

/-- Interpret propositions in one snapshot. A request is pending in `trying`
or `checked`; entering `critical` fulfils it. -/
def label (s : State) : Valuation Atom
  | .requesting t => pc s t == .trying || pc s t == .checked
  | .inCritical t => pc s t == .critical
  | .lockHeld => s.locked

/-! ## One transition schedules one instruction -/

/-- Given the protocol mode, current instruction and shared bit, return the
updated instruction and bit. A failed test spins; a broken successful test
only records `checked`, while an atomic one also claims the lock. -/
def instruction (mode : Mode) (p : PC) (locked : Bool) : PC × Bool :=
  match p with
  | .idle => (.trying, locked)
  | .trying => if locked then (.trying, locked)
      else if mode = .broken then (.checked, locked) else (.critical, true)
  | .checked => (.critical, true)
  | .critical => (.idle, false)

/-- Execute the chosen thread's instruction, updating its counter and the
shared bit while leaving the other thread's counter untouched. -/
def advance (mode : Mode) (thread : Thread) (s : State) : State :=
  let result := instruction mode (pc s thread) s.locked
  match thread with
  | .zero => { s with pc0 := result.1, locked := result.2 }
  | .one => { s with pc1 := result.1, locked := result.2 }

-- These rewrites let later proofs track an unscheduled thread without
-- repeatedly unfolding the global-state update.
@[simp] theorem advance_zero_preserves_pc1 (m : Mode) (s : State) :
    (advance m .zero s).pc1 = s.pc1 := rfl
@[simp] theorem advance_one_preserves_pc0 (m : Mode) (s : State) :
    (advance m .one s).pc0 = s.pc0 := rfl

/-- Both threads begin idle with a free lock, establishing the invariant's base case. -/
def initial : State := ⟨.idle, .idle, false⟩
/-- Build the finite Kripke model for a mode. The two successors represent
the scheduler's choices; neither thread is required to be chosen eventually.
The singleton initial set and `label` complete the data KILT needs. -/
def model (mode : Mode) : FiniteKripke State Atom where
  initials := {initial}
  initials_nonempty := by simp
  successors s := {advance mode .zero s, advance mode .one s}
  label := label
/-- Fix split test/claim for the safety counterexample. -/
abbrev broken := model .broken
/-- Fix atomic test-and-claim for the invariant and starvation examples. -/
abbrev atomic := model .atomic

/-- Scheduling thread zero always gives a legal successor, including a busy-wait
step. This supplies the no-deadlock proof required by `checkAgainst`. -/
theorem serial (mode : Mode) : (model mode).toKripke.Serial := by
  intro s
  exact ⟨advance mode .zero s, by change _ ∈ ({_, _} : Finset State); simp⟩

-- Check seriality, then inspect spinning, atomic acquisition, split testing
-- and release on concrete snapshots before constructing whole executions.
example : broken.isSerial = true := broken.isSerial_eq_true_iff.mpr (serial .broken)
example : atomic.isSerial = true := atomic.isSerial_eq_true_iff.mpr (serial .atomic)
/-- A failed test is an explicit busy-wait step, not an automatically inserted loop. -/
example : advance .atomic .zero ⟨.trying, .critical, true⟩ = ⟨.trying, .critical, true⟩ := by decide
example : advance .atomic .zero ⟨.trying, .idle, false⟩ = ⟨.critical, .idle, true⟩ := by decide
example : advance .broken .zero ⟨.trying, .idle, false⟩ = ⟨.checked, .idle, false⟩ := by decide
example : advance .atomic .zero ⟨.critical, .trying, true⟩ = ⟨.idle, .trying, false⟩ := by decide

/-! ## Supplying an execution and writing its properties -/

/-- Start at `initial`; `schedule n` chooses the thread for the transition
from position `n` to `n + 1`. An infinite schedule defines a full state trace. -/
def execution (mode : Mode) (schedule : Nat → Thread) : Nat → State
  | 0 => initial
  | n+1 => advance mode (schedule n) (execution mode schedule n)

/-- Attach transition proofs to the scheduled trace, allowing it to be used
with KILT's path semantics and its induced valuation word. -/
def scheduledPath (mode : Mode) (schedule : Nat → Thread) : (model mode).toKripke.Path where
  states := ⟨execution mode schedule⟩
  valid n := by
    change advance mode (schedule n) _ ∈ ({_, _} : Finset State)
    cases schedule n <;> simp

/-- Certify the starting state so this path can instantiate a model-satisfaction claim. -/
theorem scheduledPath_initial (mode : Mode) (schedule : Nat → Thread) :
    (scheduledPath mode schedule).IsInitial := by change initial ∈ ({initial} : Finset State); simp

/-- Lift the chosen thread's critical-section observation into formula syntax. -/
def critical (t : Thread) : Formula Atom := .atom (.inCritical t)
/-- Lift its pending-request observation, including the broken `checked` position. -/
def request (t : Thread) : Formula Atom := .atom (.requesting t)
/-- Safety: at no position may both threads be in their critical sections. -/
def mutualExclusion : Formula Atom := □ (¬ₗ (critical .zero ∧ₗ critical .one))
/-- Liveness: every pending request of thread `t` must eventually enter its
critical section. Mutual exclusion alone does not guarantee this. -/
def starvationFreedom (t : Thread) : Formula Atom := □ (request t ⟹ ◇ critical t)
/-- A snapshot-level collision test, used to expose a finite witness of the
global safety failure before interpreting it through labels. -/
def bothCritical (s : State) : Prop := s.pc0 = .critical ∧ s.pc1 = .critical

/-- Make concrete collision tests reducible by `decide` using counter equality. -/
instance (s : State) : Decidable (bothCritical s) :=
  inferInstanceAs (Decidable (s.pc0 = .critical ∧ s.pc1 = .critical))

/-! ## Split test/claim admits a finite safety violation -/

/-- Schedule 0, 0, 1, 1, 0, 1 so both threads pass the test before either
claims the lock. The default of thread zero makes the schedule infinite. -/
def raceSchedule (n : Nat) : Thread :=
  ([.zero, .zero, .one, .one, .zero, .one] : List Thread)[n]?.getD .zero

/-- Reuse `scheduledPath` to carry the transition proofs for this interleaving. -/
def racePath := scheduledPath .broken raceSchedule
example : (racePath.states 2) = ⟨.checked, .idle, false⟩ := by decide
example : (racePath.states 4) = ⟨.checked, .checked, false⟩ := by decide
/-- After six transitions both threads are critical, a finite safety witness. -/
theorem race_collision : bothCritical (racePath.states 6) := by decide

/-- Lift the collision on one initial execution into failure of universal
mutual exclusion; its later continuation cannot undo the bad position. -/
theorem broken_not_mutualExclusion : ¬ broken.toKripke.Satisfies mutualExclusion := by
  intro h
  have hall := sat_globally.mp (h racePath (scheduledPath_initial _ _))
  have hbad := hall 6 (by omega)
  apply hbad
  rw [sat_conj]
  change label (racePath.states 6) (.inCritical .zero) = true ∧
    label (racePath.states 6) (.inCritical .one) = true
  constructor <;> decide

/-! ## Atomic acquisition preserves mutual exclusion -/

/-- Record the facts needed for induction: `checked` is unreachable, a critical
thread holds the lock, and the threads are not critical together. This is a
predicate to prove along atomic paths, not a restriction on the shared carrier. -/
def AtomicInvariant (s : State) : Prop :=
  s.pc0 ≠ .checked ∧ s.pc1 ≠ .checked ∧
  (s.pc0 = .critical → s.locked = true) ∧
  (s.pc1 = .critical → s.locked = true) ∧ ¬ bothCritical s

/-- If the invariant holds before an allowed atomic step, it holds afterward,
whichever thread the scheduler chooses. -/
theorem atomic_step_invariant (s : State) (hi : AtomicInvariant s)
    (t : State) (ht : t ∈ atomic.successors s) : AtomicInvariant t := by
  rcases s with ⟨p0, p1, locked⟩
  simp only [model, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;>
    cases p0 <;> cases p1 <;> cases locked <;>
    simp_all [AtomicInvariant, bothCritical, advance, instruction, pc]

/-- Use the initial-state proof for the base case and step preservation for
induction over every position of any initial atomic execution. -/
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

/-- Translate the preserved snapshot invariant into the global LTL safety property. -/
theorem atomic_mutualExclusion : atomic.toKripke.Satisfies mutualExclusion := by
  intro path hi
  apply sat_globally.mpr
  intro i _
  have hs := (atomic_path_invariant path hi i).2.2.2.2
  rw [sat_neg, sat_conj]
  change ¬ (label (path.states i) (.inCritical .zero) = true ∧
    label (path.states i) (.inCritical .one) = true)
  simpa [bothCritical, label, pc] using hs

/-! ## Atomicity still permits starvation without fairness -/

/-- Let thread zero request in the first transition, then schedule only thread
one. That thread keeps running while zero's request is never served. -/
def unfairSchedule (n : Nat) : Thread := if n = 0 then .zero else .one
/-- The unfair schedule is still a legal initial execution of the atomic model. -/
def unfairPath := scheduledPath .atomic unfairSchedule

/-- From position one onward, zero stays in `trying`; this excludes every
proposed future witness of entry to its critical section. -/
theorem unfair_waits : ∀ n, (unfairPath.states (n+1)).pc0 = .trying := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (advance .atomic (unfairSchedule (n+1)) _).pc0 = .trying
    change (execution .atomic unfairSchedule (n+1)).pc0 = .trying at ih
    simpa [unfairSchedule, advance] using ih

/-- The request at position one has no eventual critical-section response. -/
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

/-- One legal unfair execution refutes starvation freedom for the whole model. -/
theorem atomic_not_starvationFree : ¬ atomic.toKripke.Satisfies (starvationFreedom .zero) :=
  fun h => unfair_not_response (h unfairPath (scheduledPath_initial _ _))

/-! ## Passing a monitor and its meaning to the checker

`checkAgainst` takes a violation automaton and a seriality proof. Here
`notResponse (requesting zero) (inCritical zero)` accepts exactly an execution
with an unanswered request by thread zero. Its `notResponse_accepts` theorem
supplies that meaning to `checkAgainst_correct`; the `_` arguments are the
monitor and formula inferred by Lean. Formula-input checking is available
separately; this example keeps the supplied-monitor contract visible.
-/

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

/-- Consume the false verdict and the monitor's language theorem to recover
the corresponding failure of the LTL specification. -/
theorem atomic_not_starvationFree_from_checker :
    ¬ atomic.toKripke.Satisfies (starvationFreedom .zero) := by
  intro h
  have hc := (atomic.checkAgainst_correct _ (serial .atomic) _
    (Monitors.notResponse_accepts (Atom.requesting .zero) (Atom.inCritical .zero))).mpr h
  rw [atomic_response_check] at hc
  cases hc

-- Display finite prefixes of the two explicitly constructed infinite paths,
-- then the full state count, reachable counts and supplied-monitor verdict.
-- These prefixes are illustrations, not lassos returned by the checker.
#eval (List.range 7).map (fun n => racePath.states n)
#eval (List.range 9).map (fun n => unfairPath.states n)
#eval Fintype.card State
#eval (broken.reachableSet.card, atomic.reachableSet.card)
#eval atomic.checkAgainst (Monitors.notResponse (Atom.requesting .zero) (Atom.inCritical .zero))
  (serial .atomic)
end Examples.TwoThreadLock
