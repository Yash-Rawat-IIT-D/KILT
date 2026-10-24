import KILT.LTL.Compile
import KILT.Graph.Enumeration

/-!
# Executable compiler-state traversal

Formula preorder determines a finite atom-order-independent traversal. Assignments
exclude before including each subformula, then filter consistency. Counters use
increasing numeric order. This order selects witnesses, not accepted languages.
-/
namespace KILT.LTL
universe u
variable {AP : Type u} [DecidableEq AP]

namespace Tableau

def subformulaOrder (f : NNF AP) : Graph.Enumeration (NNF.Subformula f) :=
  Graph.Enumeration.ofList ((preorder f).pmap
    (fun g hg => (⟨g, hg⟩ : NNF.Subformula f))
    (by intro g hg; exact mem_preorder.mp hg)) (by
      rintro ⟨g, hg⟩
      exact List.mem_pmap.mpr ⟨g, mem_preorder.mpr hg, rfl⟩)

def stateOrder (f : NNF AP) : Graph.Enumeration (State f) :=
  (subformulaOrder f).finset.subtype StaticConsistent

end Tableau
namespace Formula

def automatonOrder (φ : Formula AP) : Graph.Enumeration (AutomatonState φ) :=
  (Tableau.stateOrder φ.normalize).product
    (Graph.Enumeration.fin (max 1 (Tableau.toGeneralizedBuchi φ.normalize).accepting.length))

end Formula
end KILT.LTL
