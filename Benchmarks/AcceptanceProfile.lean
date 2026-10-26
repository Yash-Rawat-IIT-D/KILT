import KILT.Kripke.OrderedCheck
import Examples.Buchi
import Examples.TrafficLight
import Examples.Counterexample

/-!
Counterbalanced interpreted profiling of the pre-P2 and current lasso engines.
The baseline candidate/forest logic is copied from cfce280; shared preparation
and parent operations were unchanged by P1/P2. This benchmark is not a library
backend and is outside the default build and axiom-audit import closure.
-/
namespace Benchmarks.AcceptanceProfile
open KILT KILT.Graph KILT.LTL KILT.Automata
set_option synthInstance.maxSize 1024
set_option maxRecDepth 16384

private def baselineCandidate (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds accepting : Finset g.Vertex) (stems : FiniteGraph.ParentForest g order seeds)
    (q : g.Vertex) : Option (Lasso g.Vertex) :=
  if q ∈ accepting then
    if stems.reached q then
      let returns := g.parentsTo order (g.successors q) q
      if returns.reached then
        (stems.route? q).bind fun stem =>
          returns.route?.map fun back =>
            ⟨stem.dropLast, q :: back.dropLast, List.cons_ne_nil _ _⟩
      else none
    else none
  else none

private def baselineFinite (g : FiniteGraph) (order : Enumeration g.Vertex)
    (seeds accepting : Finset g.Vertex) : Option (Lasso g.Vertex) :=
  let stems := g.parentForest order seeds
  order.states.findSome? (baselineCandidate g order seeds accepting stems)

private def baselinePrepared {S : Type} [Fintype S] [DecidableEq S]
    {seeds : Finset S} {next : S → Finset S} (p : PreparedReachable seeds next)
    (order : Enumeration S) (accepting : Finset S) : Option (Lasso S) :=
  (baselineFinite p.graph (p.order order) p.initials (p.accepting accepting)).map
    (Lasso.map p.decode)

private def baselineLasso {S : Type} [Fintype S] [DecidableEq S]
    (order : Enumeration S) (seeds : Finset S) (next : S → Finset S)
    (accepting : Finset S) : Option (Lasso S) :=
  if seeds = ∅ ∨ accepting = ∅ then none else
    baselinePrepared (prepareReachable order seeds next) order accepting

@[noinline] private def execute {A B : Type} (f : A → B) (input : A) : IO B :=
  pure (f input)

@[noinline] private def timedBatch {A B : Type} (label : String)
    (count : Nat) (input : A) (f : A → B) : IO B := do
  let start ← IO.monoNanosNow
  let mut result ← execute f input
  for _ in List.range (count - 1) do
    result ← execute f input
  let stop ← IO.monoNanosNow
  IO.println s!"PROFILE {label} {stop - start} ns count={count}"
  return result

private def sameWitness {S : Type} [DecidableEq S]
    (name : String) (first second : Option (Lasso S)) : IO Unit := do
  unless first.map (fun l => (l.prefix, l.loop)) ==
      second.map (fun l => (l.prefix, l.loop)) do
    throw (IO.userError s!"profile witness mismatch: {name}")

private def pair {A S : Type} [DecidableEq S] (name : String) (count : Nat)
    (reverse : Bool) (input : A) (old new : A → Option (Lasso S)) : IO Unit := do
  let (a, b) ← if reverse then do
      let b ← timedBatch s!"{name}/new" count input new
      let a ← timedBatch s!"{name}/old" count input old
      pure (a, b)
    else do
      let a ← timedBatch s!"{name}/old" count input old
      let b ← timedBatch s!"{name}/new" count input new
      pure (a, b)
  sameWitness name a b

/-- Recreate cfce280's derived enumeration constructors, including dedup passes. -/
private def legacyProduct {S T : Type} [DecidableEq S] [DecidableEq T]
    (a : Enumeration S) (b : Enumeration T) : Enumeration (S × T) :=
  Enumeration.ofList (a.states.flatMap fun s => b.states.map fun t => (s, t)) (by
    rintro ⟨s, t⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
    exact ⟨s, a.complete s, t, b.complete t, rfl, rfl⟩)

private def legacyOrder {AP : Type} [DecidableEq AP] (φ : Formula AP) :
    Enumeration (Formula.AutomatonState φ) :=
  let root := φ.normalize
  let subformulas := Tableau.subformulaOrder root
  let subsets := Enumeration.ofList (Enumeration.subsetList subformulas.states)
    (fun s => by simpa [Enumeration.finset, Enumeration.ofNodup] using subformulas.finset.complete s)
  let states := Enumeration.ofList
    (subsets.subtype Tableau.StaticConsistent).states
    (subsets.subtype Tableau.StaticConsistent).complete
  legacyProduct states (Enumeration.ofList
    (List.finRange (max 1 (Tableau.toGeneralizedBuchi root).accepting.length)) (by simp))

private def model {S AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (φ : Formula AP) (order : Enumeration S)
    (rounds : Nat) : IO Unit := do
  let A := φ.violationAutomaton
  let input := (order.product (Formula.neg φ).automatonOrder,
    M.productInitials A, M.productSuccessors A, FiniteKripke.productAccepting A)
  let oldOrder := legacyProduct order (legacyOrder (Formula.neg φ))
  unless oldOrder.states == input.1.states do throw (IO.userError "legacy enumeration order changed")
  let p := prepareReachable input.1 input.2.1 input.2.2.1
  let denseOrder := p.order input.1
  let mask := p.accepting input.2.2.2
  for round in List.range rounds do
    IO.println s!"ROUND {name} {round}"
    -- Same input is reused, with old/new order alternating each round.
    pair s!"{name}/full" 1 (round % 2 == 1) input
      (fun (o, s, n, a) => baselineLasso o s n a)
      (fun (o, s, n, a) => Graph.acceptingLasso? o s n a)
    pair s!"{name}/order-control" 1 (round % 2 == 1) (oldOrder, input)
      (fun (o, (_, s, n, a)) => Graph.acceptingLasso? o s n a)
      (fun (_, (o, s, n, a)) => Graph.acceptingLasso? o s n a)
    pair s!"{name}/prepared" 25 (round % 2 == 1) (p, input.1, input.2.2.2)
      (fun (p, o, a) => baselinePrepared p o a)
      (fun (p, o, a) => p.acceptingLasso? o a)
    pair s!"{name}/dense" 25 (round % 2 == 1) (denseOrder, p.initials, mask)
      (fun (o, s, a) => baselineFinite p.graph o s a)
      (fun (o, s, a) => p.graph.acceptingLasso? o s a)
    let _ ← timedBatch s!"{name}/preparation-control" 1
      (input.1, input.2.1, input.2.2.1) (fun (o, s, n) => (prepareReachable o s n).graph)
  IO.println s!"VALIDATED {name} exact paired witnesses"

def run (rounds : Nat) : IO Unit := do
  model "waiting-response" Examples.Buchi.waitingSystem Examples.RequestGrant.response
    Examples.Counterexample.requestOrder rounds
  model "traffic-response" Examples.TrafficLight.controller Examples.TrafficLight.redResponds
    Examples.Counterexample.trafficOrder rounds

end Benchmarks.AcceptanceProfile

def main (args : List String) : IO Unit := do
  let rounds := (args.head?.bind String.toNat?).getD 6
  if rounds = 0 then throw (IO.userError "rounds must be positive")
  Benchmarks.AcceptanceProfile.run rounds
