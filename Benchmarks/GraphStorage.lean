import KILT.Kripke.OrderedCheck
import KILT.Graph.Parents
import Examples.Buchi
import Examples.TrafficLight
import Examples.Counterexample
import Examples.Tableau

/-! Explicit evaluation of the canonical graph backend, outside default builds.
Historical cached/indexed comparisons are reproducible from commit 2535acf;
this harness no longer imports the retired backends. -/
open KILT KILT.LTL KILT.Automata
set_option synthInstance.maxSize 1024
set_option maxRecDepth 16384
namespace Benchmarks.GraphStorage

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
  let new ← timed s!"{name}/boolean" input (fun (order, seeds, next, acc) =>
    Graph.hasAcceptingCycleWithOrder order seeds next acc)
  let newLasso ← timed s!"{name}/lasso" input (fun (order, seeds, next, acc) =>
    Graph.acceptingLasso? order seeds next acc)
  unless newLasso.isSome == new do throw (IO.userError s!"{name}: witness/verdict mismatch")
  if let some l := newLasso then
    unless Examples.Counterexample.certificateValid seeds next acc l do
      throw (IO.userError s!"{name}: invalid lasso")
    IO.println s!"LASSO {name} prefix={l.prefix.length} loop={l.loop.length}"
    IO.println s!"WITNESS {name} prefixRanks={l.prefix.map (fun s => (order.rank s).val)} loopRanks={l.loop.map (fun s => (order.rank s).val)}"
  let p ← timed (B := fun inp : Graph.Enumeration S × Finset S × (S → Finset S) =>
      Graph.PreparedReachable inp.2.1 inp.2.2)
    s!"{name}/prepare" (order, seeds, next) (fun inp =>
      Graph.prepareReachable inp.1 inp.2.1 inp.2.2)
  let answer ← timed s!"{name}/prepared-search" (p, acc) (fun (p, acc) =>
    p.hasAcceptingCycle acc)
  unless new == answer do throw (IO.userError s!"{name}: prepared verdict mismatch")
  let preparedWitness ← timed s!"{name}/prepared-lasso" (p, acc) (fun (p, acc) =>
    p.acceptingLasso? order acc)
  unless preparedWitness.map (fun l => (l.prefix, l.loop)) ==
      newLasso.map (fun l => (l.prefix, l.loop)) do
    throw (IO.userError s!"{name}: prepared exact witness mismatch")
  let forest ← timed (B := fun p : Graph.PreparedReachable seeds next =>
      Graph.FiniteGraph.ParentForest p.graph (p.order order) p.initials) s!"{name}/parent-search" p
    (fun p => p.graph.parentForest (p.order order) p.initials)
  let routes ← timed s!"{name}/reconstruct-all-for-validation" forest
    (fun forest => (List.finRange p.graph.size).map fun target =>
      forest.route? target)
  for target in List.finRange p.graph.size do
    let actual := routes[target.val]!.map (List.map p.decode)
    match actual with
    | none => throw (IO.userError s!"{name}: prepared reachable vertex has no route")
    | some path =>
      unless path.head?.any (fun s => decide (s ∈ seeds)) &&
          path.getLast? == some (p.decode target) &&
          (path.zip path.tail).all (fun (s, t) => decide (t ∈ next s)) do
        throw (IO.userError s!"{name}: invalid reconstructed route")
  IO.println s!"ROUTES {name} {routes.map (Option.map (List.map (fun i => (order.rank (p.decode i)).val)))}"
  IO.println s!"COUNTS {name} full={Fintype.card S} reachable={p.graph.size} edges={(p.graph.adjacency.map Array.size).foldl (· + ·) 0} parents={forest.storage.entries.size} successorRows={(p.graph.size)} verdict={answer}"

def formulaCase {S AP : Type} [Fintype S] [DecidableEq S] [DecidableEq AP]
    (name : String) (M : FiniteKripke S AP) (φ : Formula AP) (hs : M.toKripke.Serial)
    (order : Graph.Enumeration S) : IO Unit := do
  let standard ← timed s!"{name}/check" φ (fun φ => M.check φ hs)
  let ordered ← timed s!"{name}/checkWithOrder" φ (fun φ => M.checkWithOrder φ hs order)
  unless standard == ordered do throw (IO.userError s!"{name}: public check mismatch")
  let witness ← timed s!"{name}/formula-counterexample" φ (fun φ => M.counterexample? φ hs order)
  unless witness.isSome == !standard do throw (IO.userError s!"{name}: formula witness mismatch")
  let A := φ.violationAutomaton
  let productOrder := order.product (Formula.neg φ).automatonOrder
  if let some l := witness then
    unless Examples.Counterexample.certificateValid (M.productInitials A)
        (M.productSuccessors A) (FiniteKripke.productAccepting A) l do
      throw (IO.userError s!"{name}: invalid formula witness")
    IO.println s!"FORMULA_WITNESS {name} prefixRanks={l.prefix.map (fun s => (productOrder.rank s).val)} loopRanks={l.loop.map (fun s => (productOrder.rank s).val)}"
  else IO.println s!"FORMULA_WITNESS {name} none"
  let prepared ← timed (B := fun φ : Formula AP =>
      M.PreparedProduct φ.violationAutomaton order (Formula.neg φ).automatonOrder)
    s!"{name}/prepare-product" φ (fun φ =>
      M.prepareProduct φ.violationAutomaton order (Formula.neg φ).automatonOrder)
  unless prepared.hasAcceptingCycle == !standard do throw (IO.userError s!"{name}: prepared product mismatch")
  graphCase name (order.product (Formula.neg φ).automatonOrder)
    (M.productInitials A) (M.productSuccessors A) (FiniteKripke.productAccepting A)

def chain (s : Fin 24) : Finset (Fin 24) :=
  if h : s.val + 1 < 24 then {⟨s.val + 1, h⟩} else {s}

def sparse (s : Fin 128) : Finset (Fin 128) :=
  if s = 0 then {5, 7} else if s = 5 ∨ s = 7 then {9} else {s}

def wide (s : Fin 64) : Finset (Fin 64) :=
  if s = 0 then Finset.univ.erase 63 else {s}

def terminal (s : Fin 24) : Finset (Fin 24) :=
  if h : s.val + 1 < 24 then {⟨s.val + 1, h⟩} else ∅

def enumerationCases : IO Unit := do
  let numbers ← timed "enumeration/fin" 512 Graph.Enumeration.fin
  unless numbers.states.length == 512 do throw (IO.userError "fin enumeration size")
  let pairs ← timed "enumeration/product" (Graph.Enumeration.fin 32, Graph.Enumeration.fin 16)
    (fun (a, b) => a.product b)
  unless pairs.states.length == 512 do throw (IO.userError "product enumeration size")
  let filtered ← timed "enumeration/subtype" numbers
    (fun order => order.subtype (fun i => i.val % 2 = 0))
  unless filtered.states.length == 256 do throw (IO.userError "subtype enumeration size")
  let subsets ← timed "enumeration/powerset" (Graph.Enumeration.fin 8)
    Graph.Enumeration.finset
  unless subsets.states.length == 256 do throw (IO.userError "powerset enumeration size")

def isolatedModel : FiniteKripke (Fin 64) Nat where
  initials := {0}
  initials_nonempty := ⟨0, by simp⟩
  successors := fun s => {s}
  label := fun _ _ => false

def isolatedAutomaton : FiniteBuchi (Fin 16) (Valuation Nat) where
  initials := {0}
  successors := fun q _ => {q}
  accepting := Finset.univ

def additionalCases : IO Unit := do
  let prepared ← timed "sparse-product/prepare" () (fun _ =>
    isolatedModel.prepareProduct isolatedAutomaton (Graph.Enumeration.fin 64) (Graph.Enumeration.fin 16))
  unless prepared.hasAcceptingCycle do throw (IO.userError "sparse product must accept")
  match prepared with
  | .empty _ => throw (IO.userError "sparse product unexpectedly empty")
  | .ready data =>
      unless data.carrier.graph.size == 1 do throw (IO.userError "sparse product reachable size")
      IO.println s!"PRODUCT sparse-product full=1024 reachable={data.carrier.graph.size}"
  let yes ← timed "tableau/literal-match" Examples.Tableau.literal (fun s =>
    (Tableau.successors s Examples.Tableau.onlyP).card)
  let no ← timed "tableau/literal-mismatch" Examples.Tableau.literal (fun s =>
    (Tableau.successors s Examples.Tableau.off).card)
  unless yes > 0 && no == 0 do throw (IO.userError "tableau literal successors")
  IO.println s!"TABLEAU match={yes} mismatch={no}"

def run (runs : Nat) : IO Unit := do
  for sample in List.range runs do
    IO.println s!"REPETITION {sample + 1}/{runs}"
    enumerationCases
    additionalCases
    graphCase "no-reachable-acceptance" (Graph.Enumeration.fin 64) {0} wide {63}
    graphCase "accepting-deadlock" (Graph.Enumeration.fin 24) {0} terminal {23}
    graphCase "chain" (Graph.Enumeration.fin 24) {0} chain {23}
    graphCase "mostly-unreachable" (Graph.Enumeration.fin 128) {0} sparse {9}
    formulaCase "waiting-response" Examples.Buchi.waitingSystem Examples.RequestGrant.response
      Examples.Buchi.waitingSerial Examples.Counterexample.requestOrder
    formulaCase "traffic-response" Examples.TrafficLight.controller Examples.TrafficLight.redResponds
      Examples.TrafficLight.controller_serial Examples.Counterexample.trafficOrder
  IO.println "All graph verdict, witness and route validations passed."

end Benchmarks.GraphStorage

def main (args : List String) : IO Unit := do
  let runs := (args.head?.bind String.toNat?).getD 3
  if runs = 0 then throw (IO.userError "runs must be positive")
  Benchmarks.GraphStorage.run runs
