import KILT

/-!
# A small frontend session, including its limits

This file needs only `import KILT`. The frontend saves proof boilerplate for
small concrete instances; the semantic API remains available for symbolic
reasoning. The `#eval` displays execute the checker and do not create proofs.
-/

namespace Examples.Frontend
open KILT KILT.LTL
open scoped KILT.LTL

inductive State where
  | waiting
  | granted
  deriving DecidableEq, Repr

def stateOrder : Graph.Enumeration State :=
  Graph.Enumeration.ofList [.waiting, .granted] (by intro s; cases s <;> simp)

instance : Fintype State := stateOrder.fintype

/-- Atom zero means grant; atom one means request. All other atoms are false. -/
def model (allowWaiting : Bool) : FiniteKripke State Nat where
  initials := {.waiting}
  initials_nonempty := by simp
  successors
    | .waiting => if allowWaiting then {.waiting, .granted} else {.granted}
    | .granted => {.granted}
  label state atom := match state with
    | .waiting => atom == 1
    | .granted => atom == 0

theorem serial (allowWaiting : Bool) : (model allowWaiting).toKripke.Serial := by
  cases allowWaiting <;> kilt_serial

abbrev healthy := model false
abbrev mayWait := model true
def eventuallyGrant : Formula Nat := ◇ (.atom 0)

/-- Before: explicitly connect a concrete verdict to the semantic theorem. -/
theorem healthy_explicit : healthy.toKripke.Satisfies eventuallyGrant := by
  apply (healthy.check_correct eventuallyGrant (serial false)).mp
  kilt_decide

/-- After: one invocation performs the same proof steps. -/
theorem healthy_verified : healthy.toKripke.Satisfies eventuallyGrant := by
  kilt_verify (serial false)

/-- A false verdict can also be proved; `kilt_verify` cannot prove the false
claim that this model universally grants. No fairness excludes waiting forever. -/
theorem waiting_verdict : mayWait.check eventuallyGrant (serial true) = false := by
  kilt_decide

/-- Presentation uses the existing prepared API and performs extraction once.
Unexpected execution results fail the examples build, but are not proofs. -/
def display (allowWaiting : Bool) : IO Unit := do
  let query := ((model allowWaiting).checker (serial allowWaiting) stateOrder).prepare eventuallyGrant
  let result := query.runSystem
  unless result.verdict == !allowWaiting && result.counterexample?.isSome == allowWaiting do
    throw (IO.userError "frontend regression: unexpected verdict or witness presence")
  IO.println s!"allow waiting={allowWaiting}\n{result.renderRepr 6}"

#eval display false
#eval display true

/-!
## A valid proof outside computational automation's scope

The graph below is a single self-loop, but its labels are an unknown function.
The hypothesis `hv` tells us atom zero holds. `kilt_verify` cannot compute that
symbolic value or use `hv` as a general proof-search hint. A direct semantic
proof still works. This limitation is checked without relying on a timeout.
-/

def labelledLoop (v : Valuation Nat) : FiniteKripke Unit Nat where
  initials := {()}
  initials_nonempty := by simp
  successors _ := {()}
  label _ := v

theorem labelledLoop_serial (v : Valuation Nat) : (labelledLoop v).toKripke.Serial := by
  -- Even here the goal contains v: these computation macros require closed goals.
  fail_if_success kilt_serial
  intro state
  exact ⟨(), by simp [FiniteKripke.toKripke, labelledLoop]⟩

theorem symbolic_manual (v : Valuation Nat) (hv : v 0 = true) :
    (labelledLoop v).toKripke.Satisfies (.atom 0) := by
  fail_if_success kilt_verify (labelledLoop_serial v)
  intro path initial
  change v 0 = true
  exact hv

/-- Once the valuation is concrete, computation can close the same kind of goal. -/
theorem concrete_verified :
    (labelledLoop (fun atom => atom == 0)).toKripke.Satisfies (.atom 0) := by
  kilt_verify (labelledLoop_serial _)

/-!
The other limit is cost: kernel reduction can become expensive as models and
tableaux grow, even when compiled `#eval` is practical. These macros add no
performance improvement or native proof oracle. For larger examples, use the
existing execution API and distinguish its printed results from theorem proofs.
-/

end Examples.Frontend
