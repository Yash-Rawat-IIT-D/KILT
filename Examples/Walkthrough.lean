import KILT

/-!
# A Demo KILT session: model, formula, proof, counterexample


The system starts waiting for a grant. The healthy version must grant on its
first step. The other version may wait forever, although granting is possible.
Both versions are serial; no fairness restricts the nondeterministic choices.

There are three different outputs to which demonstrates what KILT does:

* `#eval` executes code and displays data (it does not produce a theorem)
* A `theorem` is a proof checked by Lean, including the concrete verdict proofs.
* `counterexample?` returns optional finite data describing an infinite trace.

From the repository root, after building the library, rerun the displays with:
`LEAN_NUM_THREADS=1 lake env lean Examples/Walkthrough.lean`.
The normal examples build also imports and checks this file.
-/

namespace Examples.Walkthrough
open KILT KILT.LTL
open scoped KILT.LTL

/-! ## 1. Inputs: state names, atom names, and a complete state order -/

inductive State where
  | waiting
  | granted
  deriving DecidableEq, Repr

inductive Atom where
  | request
  | grant
  deriving DecidableEq, Repr

/-- The order is also the deterministic tie-breaker when choosing witnesses. -/
def stateOrder : Graph.Enumeration State :=
  Graph.Enumeration.ofList [.waiting, .granted] (by intro s; cases s <;> simp)

-- Derive finite-state enumeration from this one order. Atom finiteness is not
-- needed: Atom only needs decidable equality for formula compilation.
instance : Fintype State := stateOrder.fintype

/-- A label is a Boolean assignment to every atom, separately for each state. -/
def label : State → Valuation Atom
  | .waiting, .request => true
  | .granted, .grant => true
  | _, _ => false

/-! ## 2. Supply the finite model and its seriality proof -/

/-- Granting is always possible; `allowWaiting` additionally permits waiting. -/
def model (allowWaiting : Bool) : FiniteKripke State Atom where
  initials := {.waiting}
  initials_nonempty := by simp
  successors
    | .waiting => if allowWaiting then {.waiting, .granted} else {.granted}
    | .granted => {.granted}
  label := label

abbrev healthy := model false
abbrev mayWait := model true

/-- Every state has a successor, including states outside a particular path. -/
theorem serial (allowWaiting : Bool) : (model allowWaiting).toKripke.Serial := by
  cases allowWaiting <;> kilt_serial

-- The proof is an input to the public checker. It does not change transitions
-- or force the scheduler to take a granting edge. Partial models are allowed
-- in lower-level APIs, but require different consideration at this boundary.

/-! ## 3. Write properties, and observe the source label at position zero -/

def request : Formula Atom := .atom .request
def grant : Formula Atom := .atom .grant
def eventuallyGrant : Formula Atom := ◇ grant
def response : Formula Atom := □ (request ⟹ ◇ grant)

-- Compare the types in Infoview: State is a model state; Atom is a name;
-- label s is a valuation; a path's word is the sequence of those valuations.
#eval stateOrder.states.map fun s => (s, label s .request, label s .grant)

-- The first word position is waiting's label: request=true, grant=false.
-- "Eventually" includes position zero; "next" examines the successor label.

/-! ## 4. One direct semantic proof, without running the checker -/

/-- Every initial healthy execution observes grant at position one. -/
theorem healthy_eventually_direct : healthy.toKripke.Satisfies eventuallyGrant := by
  -- Universal satisfaction: choose an arbitrary valid infinite initial path.
  intro path initial
  have starts : path.states 0 = .waiting := by
    simpa [Kripke.Path.IsInitial, FiniteKripke.toKripke, healthy, model] using initial
  have firstStep := path.valid 0
  have grants : path.states 1 = .granted := by
    simpa [FiniteKripke.toKripke, healthy, model, starts] using firstStep
  change Sat path.word 0 (◇ grant)
  -- Supply a temporal witness: position one is at or after zero.
  apply sat_eventually.mpr
  refine ⟨1, by omega, ?_⟩
  change label (path.states 1) .grant = true
  rw [grants]
  rfl

/-! ## 5. Computing verdicts in proofs, then using checker correctness -/

-- User-facing call: model.check property serialityProof : Bool.
-- `kilt_decide` rewrites to the verified finite specification, then uses
-- ordinary kernel `decide`. It creates a proof of the concrete equation;
-- unlike `#eval`, it is not merely compiled output.

theorem healthy_verdict : healthy.check eventuallyGrant (serial false) = true := by
  kilt_decide

theorem waiting_verdict : mayWait.check eventuallyGrant (serial true) = false := by
  kilt_decide

/-- Here the verdict proof, rather than path induction, proves the property. -/
theorem healthy_eventually_checked : healthy.toKripke.Satisfies eventuallyGrant :=
  (healthy.check_correct eventuallyGrant (serial false)).mp healthy_verdict

/-- A false verdict proves existence of an infinite initial violating path. -/
theorem waiting_has_violating_path :
    ∃ path : mayWait.toKripke.Path,
      path.IsInitial ∧ ¬ WordSat path.word eventuallyGrant :=
  (mayWait.check_eq_false_iff eventuallyGrant (serial true)).mp waiting_verdict

-- The last theorem establishes existence. It has not yet returned a route
-- that a program can print. Executable extraction is the next, separate API.

/-! ## 6. Prepare once when you want both a verdict and a witness -/

-- `checker` supplies model order/seriality once. `prepare` compiles the
-- negated property internally and builds the reachable product once.
def healthyQuery := (healthy.checker (serial false) stateOrder).prepare eventuallyGrant
def waitingQuery := (mayWait.checker (serial true) stateOrder).prepare eventuallyGrant

-- Equivalent convenience calls, useful for just one operation:
-- healthy.check eventuallyGrant (serial false)
-- mayWait.counterexample? eventuallyGrant (serial true) stateOrder
-- Calling both convenience wrappers separately repeats preparation; the
-- prepared value lets the two operations share it within one evaluation.

/-! ## 7. What extraction returns, and what Lean proves about it -/

/-- Product vertices retain both the model state and violation-automaton state. -/
abbrev Witness := Graph.Lasso (State × Formula.AutomatonState (.neg eventuallyGrant))

-- waitingQuery.counterexample? : Option Witness
-- `none`: there is no initial violating execution.
-- `some l`: finite data with l.prefix, l.loop, and a proof l.loop ≠ [].
-- Graph validity/acceptance and formula violation follow from soundness,
-- rather than being extra fields of arbitrary lasso data.

theorem waiting_query_false : waitingQuery.check = false := by
  rw [FiniteKripke.PreparedCheck.check_eq_check]
  exact waiting_verdict

theorem waiting_returns_witness : waitingQuery.counterexample?.isSome = true :=
  waitingQuery.counterexample?_isSome_iff.mpr waiting_query_false

theorem healthy_returns_none : healthyQuery.counterexample? = none :=
  healthyQuery.counterexample?_eq_none_iff.mpr healthy_eventually_checked

/-- A returned witness gives a proof-backed path of its own projected sequence. -/
theorem returned_path_violates {l : Witness}
    (returned : waitingQuery.counterexample? = some l) :
    (waitingQuery.counterexamplePath l returned).IsInitial ∧
      ¬ WordSat (waitingQuery.counterexamplePath l returned).word eventuallyGrant :=
  waitingQuery.counterexample?_sound returned

/-- Projection changes the displayed state type, without shifting time. -/
theorem returned_path_states {l : Witness}
    (returned : waitingQuery.counterexample? = some l) :
    (waitingQuery.counterexamplePath l returned).states = (l.map Prod.fst).sequence :=
  waitingQuery.counterexamplePath_states l returned

-- Both the existence and actual-trace guarantee are available as one theorem.
theorem extracted_violation : ∃ l : Witness,
    ∃ returned : waitingQuery.counterexample? = some l,
      (waitingQuery.counterexamplePath l returned).IsInitial ∧
        ¬ WordSat (waitingQuery.counterexamplePath l returned).word eventuallyGrant := by
  obtain ⟨l, returned⟩ := Option.isSome_iff_exists.mp waiting_returns_witness
  exact ⟨l, returned, returned_path_violates returned⟩

/-! ## 8. Execute, pattern-match the Option, and print the system view -/

-- This display uses compiled execution. Unexpected verdict/witness presence
-- throws an error, so the examples build fails; it does not create a proof.
def display {M : FiniteKripke State Atom} {φ : Formula Atom}
    (name : String) (query : FiniteKripke.PreparedCheck M φ)
    (expected : Bool) : IO Unit := do
  let result := query.runSystem
  unless result.verdict == expected && result.counterexample?.isSome == !expected do
    throw (IO.userError s!"walkthrough {name}: unexpected verdict or witness presence")
  IO.println s!"{name}:\n{result.renderRepr}"
  match result.counterexample? with
  | none => pure ()
  | some systemLasso =>
    let observations := (List.range 8).map fun i =>
      let s := systemLasso.sequence i
      (i, s, M.label s .request, M.label s .grant)
    IO.println s!"  (index, state, request, grant): {repr observations}"

#eval do
  display "healthy/eventual grant" healthyQuery true
  display "may wait/eventual grant" waitingQuery false
  -- A larger formula uses the same model setup and proof of seriality.
  display "healthy/response" ((healthy.checker (serial false) stateOrder).prepare response) true
  display "may wait/response" ((mayWait.checker (serial true) stateOrder).prepare response) false

/-!
## 9. Read the lasso, then try a small change

An empty prefix and loop `[waiting]` means waiting forever. More generally,
prefix `[a]` and loop `[b,c]` means a,b,c,b,c,... . The loop omits the repeated
closing endpoint; validity still requires the last loop state to reach its first.
The algorithm's chosen product witness may contain repeated system states.
It promises validity, acceptance and deterministic order-based selection, not
the shortest or simplest system lasso. Inspect the actual output above.

For mayWait, there is also a granting execution. Universal satisfaction fails
because the scheduler can choose waiting forever. Nothing here assumes fairness.

Try these separately, predicting the answer first:

1. Check `𝒩 grant` on both models: which successor choices are quantified over?
2. Check `□ (¬ₗ (request ∧ₗ grant))`: can safety hold while progress fails?
3. Make granted initial too. What changes for `request`, and for `◇ grant`?
4. Use the returned lasso's `replay 12`; explain why a finite replay alone is
   insufficient to prove a liveness violation, and where soundness uses the loop.

The named theorem proofs above are included in the standard-axiom audit.
Compilation, runtime displays, and your understanding remain separate checks.
-/

end Examples.Walkthrough
