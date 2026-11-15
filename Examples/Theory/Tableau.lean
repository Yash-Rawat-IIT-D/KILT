import KILT.LTL.Tableau

/-!
# Local tableau examples
These are finite local checks, not temporal-language verdicts. In particular,
the until self-loop below passes local rules while violating strong until.
-/
namespace Examples.Tableau
open KILT.LTL KILT.LTL.Tableau

/-- Select named formulas from the existing closure; never enlarge it. -/
def assignment (f : NNF Nat) (gs : Finset (NNF Nat)) : Assignment f :=
  Finset.univ.filter fun g => g.val ∈ gs

def state (f : NNF Nat) (gs : Finset (NNF Nat))
    (h : StaticConsistent (assignment f gs)) : State f := ⟨assignment f gs, h⟩

def p : NNF Nat := .pos 0
def q : NNF Nat := .pos 1
def off : Valuation Nat := fun _ => false
def onlyP : Valuation Nat := fun a => a == 0
def onlyQ : Valuation Nat := fun a => a == 1
def both : Valuation Nat := fun a => a == 0 || a == 1

example : Fintype.card (Assignment (.truth : NNF Nat)) = 2 := by decide
example : Fintype.card (State (.truth : NNF Nat)) = 1 := by decide
example : (initials (.truth : NNF Nat)).card = 1 := by decide
example : (initials (.falsehood : NNF Nat)) = ∅ := by decide
example : Fintype.card (State (.falsehood : NNF Nat)) = 1 := by decide
example : Holds (assignment p {q}) q = False := by decide

/-- Literal assignments are checked against the source valuation. -/
def literal : State p := state p {p} (by decide)
example : Step literal literal onlyP := by decide
example : ¬ Step literal literal off := by decide
example : ∃ s ∈ initials (.negAtom 0 : NNF Nat), Step s s off := by decide
example : ¬ ∃ s ∈ initials (.negAtom 0 : NNF Nat), Step s s onlyP := by decide

/-- The source check rejects mismatched literals before considering successors. -/
theorem literal_compatible : LiteralCompatible literal onlyP := by decide
theorem literal_incompatible : ¬ LiteralCompatible literal off := by decide
theorem mismatched_has_no_successors : successors literal off = ∅ :=
  successors_empty_of_incompatible literal off literal_incompatible
theorem matching_has_successors : (successors literal onlyP).Nonempty := by decide

/-- Both polarities may be statically present, but no source valuation supports them. -/
def conflict : NNF Nat := .conj p (.negAtom 0)
example : ∀ s ∈ initials conflict, ∀ t : State conflict, ¬ Step s t off := by decide
example : ∀ s ∈ initials conflict, ∀ t : State conflict, ¬ Step s t onlyP := by decide
example : ∃ s ∈ initials (.disj p q), Step s s onlyP := by decide
example : ¬ ∃ s ∈ initials (.conj p q), Step s s onlyP := by decide
example : ∃ s ∈ initials (.conj p q), Step s s both := by decide
example : (NNF.conj p p).subformulas.card = 2 := by decide
example : Fintype.card (State (.conj p p)) = 2 := by decide

def nx : NNF Nat := .next p
def beforeNext : State nx := state nx {nx} (by decide)
def afterNext : State nx := state nx {p} (by decide)
def emptyNext : State nx := state nx ∅ (by decide)
example : Step beforeNext afterNext off := by decide
example : ¬ Step beforeNext emptyNext off := by decide
/-- Even a true current p cannot replace the next-state requirement. -/
example : ¬ Step (state nx {nx, p} (by decide)) emptyNext onlyP := by decide

example : (Formula.next (.atom 0 : Formula Nat)).normalize = nx := rfl
example : ∃ s ∈ initials (Formula.next (.atom 0 : Formula Nat)).normalize,
    Step s afterNext off := by
  change ∃ s ∈ initials nx, Step s afterNext off
  decide

def u : NNF Nat := .until p q
def waiting : State u := state u {u, p} (by decide)
def fulfilled : State u := state u {u, q} (by decide)
def emptyUntil : State u := state u ∅ (by decide)
example : Step fulfilled emptyUntil onlyQ := by decide
example : Step waiting fulfilled onlyP := by decide
example : ¬ Step waiting emptyUntil onlyP := by decide

/-- Local recurrence can keep promising q forever; accepting sets must rule this out. -/
theorem postponed_loop : Step waiting waiting onlyP := by decide
theorem postponed_word_fails : ¬ NNF.Sat ⟨fun _ => onlyP⟩ 0 u := by
  rintro ⟨j, _, hj, _⟩
  change onlyP 1 = true at hj
  contradiction

/-- The local loop even gives an infinite initial NA run, without temporal acceptance. -/
theorem postponed_run : (toNA u).Run ⟨fun _ => onlyP⟩ ⟨fun _ => waiting⟩ := by
  constructor
  · exact (toNA_start waiting).mpr (by decide)
  · intro _; exact (toNA_transition _ _ _).mpr postponed_loop

def r : NNF Nat := .release p q
def continueRelease : State r := state r {r, q} (by decide)
def endRelease : State r := state r {r, p, q} (by decide)
def emptyRelease : State r := state r ∅ (by decide)
example : Step continueRelease continueRelease onlyQ := by decide
example : ¬ Step continueRelease emptyRelease onlyQ := by decide
example : Step endRelease emptyRelease both := by decide
example : ¬ Step (state r {r, p} (by decide)) emptyRelease onlyP := by decide

/-- Direct successor-set regressions for literal and temporal boundaries. -/
def conflictingState : State conflict := state conflict {conflict, p, .negAtom 0} (by decide)
example : successors conflictingState off = ∅ := by decide
example : successors conflictingState onlyP = ∅ := by decide

def truthState : State (.truth : NNF Nat) := state .truth {.truth} (by decide)
example : LiteralCompatible truthState off := by decide
example : afterNext ∈ successors beforeNext off := by decide
example : emptyNext ∉ successors beforeNext off := by decide
example : fulfilled ∈ successors waiting onlyP := by decide
example : emptyRelease ∉ successors continueRelease onlyQ := by decide

theorem literal_represents (i : Nat) : Represents literal ⟨fun _ => onlyP⟩ i := by
  intro g hg
  have : g = p := by simpa [p, NNF.subformulas] using hg
  subst g
  constructor
  · intro _; rfl
  · intro _; decide

example : Step literal literal onlyP :=
  step_of_represents (literal_represents 0) (literal_represents 1)

/-- (closure size, raw assignments, consistent states). -/
def counts (f : NNF Nat) : Nat × Nat × Nat :=
  (f.subformulas.card, Fintype.card (Assignment f), Fintype.card (State f))
#eval counts .truth
#eval counts (.conj p p)
#eval counts (.conj p q)
#eval counts (.disj p q)
#eval counts u
#eval counts r
end Examples.Tableau
