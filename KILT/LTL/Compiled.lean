import KILT.LTL.CompileOrder

/-! One executable compiler result: automaton, witness order and language proof. -/
namespace KILT.LTL.Formula
open Cslib.Automata
universe u
variable {AP : Type u} [DecidableEq AP]

structure Compiled (φ : Formula AP) where
  automaton : Automata.FiniteBuchi (AutomatonState φ) (Valuation AP)
  order : Graph.Enumeration (AutomatonState φ)
  accepts_iff : ∀ word, ωAcceptor.Accepts automaton.toCSLib word ↔ WordSat word φ

/-- Normalize once and assemble both executable outputs from that same root.
The result can be reused across models over the same atomic propositions. -/
def compile (φ : Formula AP) : Compiled φ :=
  let root := φ.normalize
  let generalized := Tableau.toGeneralizedBuchi root
  { automaton := generalized.toFiniteBuchi
    order := (Tableau.stateOrder root).product
      (Graph.Enumeration.fin (max 1 generalized.accepting.length))
    accepts_iff := φ.toBuchi_accepts }

@[simp] theorem compile_automaton (φ : Formula AP) : φ.compile.automaton = φ.toBuchi := rfl
@[simp] theorem compile_order (φ : Formula AP) : φ.compile.order = φ.automatonOrder := rfl

theorem compile_accepts (φ : Formula AP) (word : Word AP) :
    ωAcceptor.Accepts φ.compile.automaton.toCSLib word ↔ WordSat word φ :=
  φ.compile.accepts_iff word

end KILT.LTL.Formula
