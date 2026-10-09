import KILT.LTL.Syntax

/-!
# Syntax regression examples

These checks use kernel evaluation (`decide` and `rfl`), including derived
connective expansion and formula size. No finite atom assumption is needed.
-/

namespace Examples.Syntax

open KILT.LTL

inductive Atom where
  | request
  | grant
  deriving DecidableEq, Repr

def request : Formula Atom := .atom .request
def grant : Formula Atom := .atom .grant

example : request ≠ grant := by decide
example : Formula.next request ≠ request := by decide
example : Formula.disj request grant ≠ Formula.disj grant request := by decide
example : Formula.until request grant = Formula.until request grant := by decide

example : (Formula.falsum : Formula Atom).size = 1 := rfl
example : request.size = 1 := rfl
example : (Formula.neg request).size = 2 := rfl
example : (Formula.disj request grant).size = 3 := rfl
example : (Formula.next request).size = 2 := rfl
example : (Formula.until request grant).size = 3 := rfl
example : (Formula.eventually grant).size = 4 := rfl
example : (Formula.globally (Formula.imp request (Formula.eventually grant))).size = 12 := rfl

example : (Formula.truth : Formula Atom) = .neg .falsum := rfl
example : Formula.conj request grant = .neg (.disj (.neg request) (.neg grant)) := rfl
example : Formula.imp request grant = .disj (.neg request) grant := rfl
example : Formula.eventually grant = .until Formula.truth grant := rfl
example : Formula.globally grant = .neg (Formula.eventually (.neg grant)) := rfl
example : Formula.release request grant = .neg (.until (.neg request) (.neg grant)) := rfl

-- Infinitely many possible atom identifiers are also allowed.
example : (Formula.next (.atom 123456) : Formula Nat).size = 2 := rfl

-- Syntax and size also work without a decidable equality instance for atoms.
example (AP : Type) (a : AP) : (Formula.atom a).size = 1 := rfl

end Examples.Syntax
