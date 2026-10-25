import KILT.Kripke.IndexedCheck
import KILT.Graph.IndexedParents
import Examples.Buchi
import Examples.TrafficLight
import Examples.Counterexample

/-!
Explicit evaluation of reachable indexed storage. This compares the
committed cached Boolean backend with reachable-only preparation and dense-ID
search. Parent reconstruction is measured separately from actual lasso calls.
-/
open KILT KILT.LTL KILT.Automata
set_option synthInstance.maxSize 1024
set_option maxRecDepth 16384
namespace Benchmarks.IndexedStorage

@[noinline] def execute {A : Type} {B : A → Type} (f : (a : A) → B a) (a : A) : IO (B a) :=
  pure (f a)

@[noinline] def timed {A : Type} {B : A → Type} (label : String)
    (a : A) (f : (a : A) → B a) : IO (B a) := do
  let start ← IO.monoNanosNow
  let result ← execute f a
  let stop ← IO.monoNanosNow
  IO.println s!"TIMING {label} {stop - start} ns"
  (← IO.getStdout).flush
  return result

def graphCase {S : Type} [Fintype S] [DecidableEq S] (name : String)
    (order : Graph.Enumeration S) (seeds : Finset S) (next : S → Finset S)
    (acc : Finset S) : IO Unit := do
  let input := (order, seeds, next, acc)
  let old ← timed s!"{name}/cached-total" input (fun (_, seeds, next, acc) =>
    Graph.hasAcceptingCycle seeds next acc)
  let new ← timed s!"{name}/indexed-total" input (fun (order, seeds, next, acc) =>
    Graph.hasAcceptingCycleIndexed order seeds next acc)
  unless old == new do throw (IO.userError s!"{name}: verdict mismatch")
  let oldLasso ← timed s!"{name}/cached-lasso" input (fun (order, seeds, next, acc) =>
    Graph.acceptingLassoCached? order seeds next acc)
  let newLasso ← timed s!"{name}/indexed-lasso" input (fun (order, seeds, next, acc) =>
    Graph.acceptingLasso? order seeds next acc)
  let shape := fun result : Option (Graph.Lasso S) => result.map (fun l => (l.prefix, l.loop))
  unless shape oldLasso == shape newLasso do throw (IO.userError s!"{name}: lasso mismatch")
  if let some l := newLasso then
    unless Examples.Counterexample.certificateValid seeds next acc l do
      throw (IO.userError s!"{name}: invalid indexed lasso")
    IO.println s!"LASSO {name} prefix={l.prefix.length} loop={l.loop.length}"
  let p ← timed (B := fun inp : Graph.Enumeration S × Finset S × (S → Finset S) =>
      Graph.PreparedReachable inp.2.1 inp.2.2)
    s!"{name}/prepare" (order, seeds, next) (fun inp =>
      Graph.prepareReachable inp.1 inp.2.1 inp.2.2)
  let answer ← timed s!"{name}/prepared-search" (p, acc) (fun (p, acc) =>
    p.hasAcceptingCycle acc)
  unless old == answer do throw (IO.userError s!"{name}: prepared verdict mismatch")
  let forest ← timed (B := fun p : Graph.PreparedReachable seeds next =>
      Graph.IndexedGraph.Parents p.graph) s!"{name}/parent-search" p
    (fun p => Graph.IndexedGraph.Parents.forest p.graph (p.order order) p.initials)
  let routes ← timed s!"{name}/reconstruct-all-for-validation" forest
    (fun forest => (List.finRange p.graph.size).map fun target =>
      forest.unwind (p.graph.size + 1) target [])
  for target in List.finRange p.graph.size do
    let actual := routes[target.val]!.map (List.map p.decode)
    let expected := Graph.routeFast? order seeds next (p.decode target)
    unless actual == expected do throw (IO.userError s!"{name}: selected route mismatch")
  IO.println s!"COUNTS {name} full={Fintype.card S} reachable={p.graph.size} edges={(p.graph.adjacency.map Array.size).foldl (· + ·) 0} parents={forest.entries.size} successorRows={(p.graph.size)} verdict={answer}"

def formulaCase {S AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (φ : Formula AP) (hs : M.toKripke.Serial)
    (order : Graph.Enumeration S) : IO Unit := do
  let old ← timed s!"{name}/check" φ (fun φ => M.check φ hs)
  let new ← timed s!"{name}/checkIndexed" φ (fun φ => M.checkIndexed φ hs order)
  unless old == new do throw (IO.userError s!"{name}: public check mismatch")
  let A := φ.violationAutomaton
  graphCase name (order.product (Formula.neg φ).automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (FiniteKripke.productAccepting A)

def chain (s : Fin 24) : Finset (Fin 24) :=
  if h : s.val + 1 < 24 then {⟨s.val + 1, h⟩} else {s}

def sparse (s : Fin 128) : Finset (Fin 128) :=
  if s = 0 then {5, 7} else if s = 5 ∨ s = 7 then {9} else {s}

def run (runs : Nat) : IO Unit := do
  for sample in List.range runs do
    IO.println s!"REPETITION {sample + 1}/{runs}"
    graphCase "chain" (Graph.Enumeration.fin 24) {0} chain {23}
    graphCase "mostly-unreachable" (Graph.Enumeration.fin 128) {0} sparse {9}
    formulaCase "waiting-response" Examples.Buchi.waitingSystem Examples.RequestGrant.response
      Examples.Buchi.waitingSerial Examples.Counterexample.requestOrder
    formulaCase "traffic-response" Examples.TrafficLight.controller Examples.TrafficLight.redResponds
      Examples.TrafficLight.controller_serial Examples.Counterexample.trafficOrder
  IO.println "All indexed foundation verdict and exact-route comparisons passed."

end Benchmarks.IndexedStorage

def main (args : List String) : IO Unit := do
  let runs := (args.head?.bind String.toNat?).getD 3
  if runs = 0 then throw (IO.userError "runs must be positive")
  Benchmarks.IndexedStorage.run runs
