import Examples.Demos.Frontend

/-!
# Frontend regression checks

Successful results are kernel-checked propositions. Expected tactic failures
are checked inside completed proofs, with no admitted declarations or timeout
expectations. The standalone frontend example covers symbolic labels and
concrete specialisation as well as checked execution displays.
-/

namespace Examples.FrontendRegression
open KILT KILT.LTL
open scoped KILT.LTL
open Examples.Frontend

theorem truth_verified : healthy.toKripke.Satisfies Formula.truth := by
  kilt_verify (serial false)

theorem atom_verified :
    (labelledLoop (fun atom => atom == 0)).toKripke.Satisfies (.atom 0) := by
  kilt_verify (labelledLoop_serial _)

theorem eventually_verified : healthy.toKripke.Satisfies eventuallyGrant := by
  kilt_verify (serial false)

theorem next_verified : healthy.toKripke.Satisfies (Formula.next (.atom 0)) := by
  kilt_verify (serial false)

theorem inline_serial_verified : healthy.toKripke.Satisfies eventuallyGrant := by
  kilt_verify (show healthy.toKripke.Serial from by kilt_serial)

theorem true_verdict : healthy.check eventuallyGrant (serial false) = true := by
  kilt_decide

theorem false_verdict : mayWait.check eventuallyGrant (serial true) = false := by
  kilt_decide

theorem false_claim_rejected : True := by
  fail_if_success
    have : mayWait.toKripke.Satisfies eventuallyGrant := by
      kilt_verify (serial true)
  trivial

theorem wrong_seriality_rejected : healthy.toKripke.Satisfies eventuallyGrant := by
  fail_if_success kilt_verify (serial true)
  kilt_verify (serial false)

theorem unsupported_goal_rejected : True := by
  fail_if_success kilt_verify (serial false)
  trivial

def deadlock : FiniteKripke Unit Nat where
  initials := {()}
  initials_nonempty := by simp
  successors _ := ∅
  label _ _ := false

theorem deadlock_seriality_rejected : ¬ deadlock.toKripke.Serial := by
  fail_if_success
    have : deadlock.toKripke.Serial := by kilt_serial
  intro seriality
  obtain ⟨state, edge⟩ := seriality ()
  exact Finset.notMem_empty state edge

end Examples.FrontendRegression
