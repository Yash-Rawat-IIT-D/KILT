import Examples.Counterexample

/-!
Explicit interpreted benchmark, outside the default build. Timings execute
behind an IO call; no result here is promoted to a kernel theorem. The reference
functions retain the pre-optimization algorithms. Work accounting is a separate
instrumented ordered search, not timing overhead on the production path.
-/
open KILT KILT.LTL KILT.Automata
set_option synthInstance.maxSize 1024
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Benchmarks.Efficiency
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Supply a data argument after the clock read, so the operation cannot be
precomputed as a constant Unit thunk. Dependent outputs keep formula state types. -/
@[noinline] def execute {A : Type} {B : A → Type} (f : (input : A) → B input)
    (input : A) : IO (B input) := pure (f input)

@[noinline] def timed {A : Type} {B : A → Type} (label : String) (input : A)
    (f : (input : A) → B input) : IO (B input) := do
  let start ← IO.monoNanosNow
  let result ← execute f input
  let stop ← IO.monoNanosNow
  IO.println s!"TIMING {label} {(stop-start)/1000000} ms"
  (← IO.getStdout).flush
  return result

def assertVerdict (label : String) (actual expected : Bool) : IO Unit :=
  unless actual == expected do throw (IO.userError s!"{label}: expected {expected}, got {actual}")

/-- Early stopping alone: no successor cache. -/
def earlyOnly (seeds : Finset S) (next : S → Finset S) (acc : Finset S) : Bool :=
  let reached := Graph.reachableSetFast seeds next
  decide (∃ q ∈ reached ∩ acc, Graph.reachable? (next q) next q = true)

/-- Cache alone: same eager candidate filtering and full-round reachability. -/
def cacheOnly (seeds : Finset S) (next : S → Finset S) (acc : Finset S) : Bool :=
  let rows := Graph.prepareSuccessorSet next
  Graph.hasAcceptingCycleReference seeds (Graph.successorSetLookup rows) acc

structure Work where
  rounds : Nat := 0
  requests : Nat := 0
  candidates : Nat := 0
  deriving Repr

def reachWork (next : S → Finset S) (early : Bool) (target : Option S) :
    Nat → Finset S → Finset S × Work
  | 0, reached => (reached, {})
  | n+1, reached =>
    if early && target.any (fun q => decide (q ∈ reached)) then (reached, {}) else
    let expanded := Graph.expand next reached
    if early && decide (expanded = reached) then
      (reached, ⟨1, reached.card, 0⟩) else
    let (result, work) := reachWork next early target n expanded
    (result, ⟨work.rounds + 1, work.requests + reached.card, 0⟩)

/-- Counts are for this explicit enumeration, which can differ from the
unordered public Boolean search's candidate order. Requests count successor
function applications in expansions and return-seed setup, not membership tests. -/
def cycleWork (order : Graph.Enumeration S) (seeds : Finset S)
    (next : S → Finset S) (acc : Finset S) (early : Bool) : Bool × Work := Id.run do
  let (reached, initial) := reachWork next early none (Fintype.card S) seeds
  let mut work := initial
  let mut found := false
  for q in order.states do
    if (!early || !found) && decide (q ∈ reached ∧ q ∈ acc) then
      let (back, count) := reachWork next early (some q) (Fintype.card S) (next q)
      found := found || decide (q ∈ back)
      work := ⟨work.rounds + count.rounds, work.requests + count.requests + 1, work.candidates + 1⟩
  return (found, work)

/-- Separately count materialized route expansions; routes remain the reference
predecessor choices. Target success does not imply the returned table is closed. -/
def routeWork (order : Graph.Enumeration S) (next : S → Finset S) (target : Option S) :
    Nat → List (S × Option (List S)) → Nat
  | 0, _ => 0
  | n+1, previous =>
    if target.any (fun q => (Graph.tableLookup none previous q).isSome) then 0 else
    let expanded := Graph.materialize order
      (Graph.expandRouteTable order next (Graph.tableLookup none previous))
    if Graph.routeGrowth (Graph.tableLookup none previous) expanded then
      1 + routeWork order next target n expanded else 1

def shape {T : Type} (result : Option (Graph.Lasso T)) :=
  result.map fun l => (l.prefix, l.loop)

/-- Reuse prepared stems to isolate return search from copying the finite lasso. -/
def witnessParts? (order : Graph.Enumeration S) (next : S → Finset S)
    (acc : Finset S) (stems : Graph.RouteTable S) : Option (S × List S × List S) :=
  order.states.findSome? fun q =>
    if q ∈ acc then
      (stems q).bind fun stem =>
        (Graph.routeFast? order (next q) next q).map fun back => (q, stem, back)
    else none

/-- Prepared-graph ablations; every variant includes its own cache, when used. -/
def graphCase (label : String) (order : Graph.Enumeration S) (seeds : Finset S)
    (next : S → Finset S) (acc : Finset S) (expected : Bool) (phasesOnly : Bool) : IO Unit := do
  IO.println s!"CASE {label}, carrier={Fintype.card S}, seeds={seeds.card}, accepting={acc.card}"
  if !phasesOnly then
   for (tag, algorithm) in [
      ("baseline", Graph.hasAcceptingCycleReference (State := S)),
      ("cache-only", cacheOnly (S := S)),
      ("early-only", earlyOnly (S := S)),
      ("combined-public", Graph.hasAcceptingCycle (State := S))] do
     let result ← timed s!"{label}/graph/{tag}" (seeds, next, acc) (fun (seeds, next, acc) => algorithm seeds next acc)
     assertVerdict tag result expected
  let rows ← timed s!"{label}/phase/cache" next (Graph.prepareSuccessors order)
  let cached := Graph.tableLookup ∅ rows
  let reached ← timed s!"{label}/phase/initial-closure" seeds (fun seeds => Graph.reachableSetFast seeds cached)
  let found ← timed s!"{label}/phase/candidates-and-returns" reached (fun reached =>
    order.states.any fun q => decide (q ∈ reached ∧ q ∈ acc) && Graph.reachable? (cached q) cached q)
  assertVerdict "phase verdict" found expected
  let stems ← timed s!"{label}/phase/stem-routes" seeds (fun seeds => Graph.storedRoutesFast order seeds cached)
  let parts ← timed s!"{label}/phase/lasso-return-search" stems (fun stems =>
    witnessParts? order cached acc (Graph.tableLookup none stems))
  let built ← timed s!"{label}/phase/lasso-construction" parts (fun parts => parts.map fun (q, stem, back) =>
    (stem.dropLast, q :: back.dropLast))
  IO.println s!"SIZE {label}: reachable={reached.card}, cacheRows={rows.length}, stemRows={stems.length}"
  for early in [false, true] do
    let (value, work) := cycleWork order seeds cached acc early
    assertVerdict "instrumented ordered verdict" value expected
    IO.println s!"WORK {label}: early={early}, {repr work}; rawSuccessorsWithCache={rows.length}"
  let routeRounds := routeWork order cached none (Fintype.card S)
    (Graph.materialize order (Graph.initialRouteTable seeds))
  IO.println s!"WORK {label}: initial-route-rounds={routeRounds}, reference={Fintype.card S}"
  let ref ← if phasesOnly then pure none else
    timed s!"{label}/graph/lasso-reference" seeds (fun seeds => Graph.acceptingLassoReference? order seeds next acc)
  let fast ← timed s!"{label}/graph/lasso-combined" seeds (fun seeds => Graph.acceptingLasso? order seeds next acc)
  assertVerdict "lasso" fast.isSome expected
  unless phasesOnly || shape ref == shape fast do throw (IO.userError "witness changed")
  unless built == shape fast do throw (IO.userError "phase witness changed")
  if let some l := fast then
    unless Examples.Counterexample.certificateValid seeds next acc l do
      throw (IO.userError "invalid returned witness")
    IO.println s!"WITNESS {label}: prefix={l.prefix.length}, loop={l.loop.length}"
    let returnRounds := routeWork order cached (some l.entry) (Fintype.card S)
      (Graph.materialize order (Graph.initialRouteTable (cached l.entry)))
    IO.println s!"WORK {label}: selected-return-rounds={returnRounds}, reference={Fintype.card S}"

/-- Formula-facing timers include compilation and enumeration inside execute. -/
def formulaCase {State AP : Type} [Fintype State] [DecidableEq State] [DecidableEq AP]
    (label : String) (M : FiniteKripke State AP) (φ : Formula AP)
    (serial : M.toKripke.Serial) (order : Graph.Enumeration State) (expected : Bool) (phasesOnly : Bool) : IO Unit := do
  let normalized ← timed s!"{label}/prepare/normalize-negation" φ (fun φ => (Formula.neg φ).normalize)
  let automatonOrder ← timed s!"{label}/prepare/automaton-order" φ (fun φ => (Formula.neg φ).automatonOrder)
  let productOrder ← timed s!"{label}/prepare/product-order" automatonOrder (fun automatonOrder => order.product automatonOrder)
  let data ← timed s!"{label}/prepare/initials-and-acceptance" φ (fun φ =>
    (M.productInitials φ.violationAutomaton, FiniteKripke.productAccepting φ.violationAutomaton))
  IO.println s!"SIZE {label}: closure={normalized.subformulas.card}, automaton={automatonOrder.states.length}"
  graphCase label productOrder data.1 (M.productSuccessors φ.violationAutomaton) data.2 expected phasesOnly
  let verdict ← timed s!"{label}/end-to-end/check" φ (fun φ => M.check φ serial)
  assertVerdict "public check" verdict (!expected)
  let witness ← timed s!"{label}/end-to-end/counterexample" φ (fun φ => M.counterexample? φ serial order)
  assertVerdict "public counterexample" witness.isSome expected
  if let some l := witness then
    unless Examples.Counterexample.certificateValid (M.productInitials φ.violationAutomaton)
        (M.productSuccessors φ.violationAutomaton) (FiniteKripke.productAccepting φ.violationAutomaton) l do
      throw (IO.userError "invalid formula-facing witness")

def cheapLine (s : Fin 12) : Finset (Fin 12) :=
  if h : s.val + 1 < 12 then {⟨s.val + 1, h⟩} else ∅

def run (runs : Nat) (phasesOnly : Bool) : IO Unit := do
  IO.println "MODE interpreted lake env lean --run; times exclude compilation; RSS includes Lean/runtime"
  for i in List.range runs do
    IO.println s!"REPETITION {i+1}/{runs}"
    formulaCase "waiting-response" Examples.Buchi.waitingSystem Examples.RequestGrant.response
      Examples.Buchi.waitingSerial Examples.Counterexample.requestOrder true phasesOnly
    formulaCase "traffic-response" Examples.TrafficLight.controller Examples.TrafficLight.redResponds
      Examples.TrafficLight.controller_serial Examples.Counterexample.trafficOrder false phasesOnly
    graphCase "cheap-chain" (Graph.Enumeration.fin 12) {0} cheapLine {11} false phasesOnly
    graphCase "cheap-self-loop" (Graph.Enumeration.fin 1) {0} (fun s => {s}) {0} true phasesOnly
  IO.println "All benchmark verdict and witness checks passed."
end Benchmarks.Efficiency

def main (args : List String) : IO Unit := do
  let runs := (args.head?.bind String.toNat?).getD 3
  if runs = 0 then throw (IO.userError "runs must be positive")
  Benchmarks.Efficiency.run runs (args[1]? == some "phases")
