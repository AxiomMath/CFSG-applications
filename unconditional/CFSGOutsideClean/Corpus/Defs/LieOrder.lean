import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSGOutside.Corpus.Defs.LieOrder
import CFSGOutsideClean.Corpus.Defs.ClassicalModel

/-!
# The copied order formulas are the corpus ones

`CFSGOutside.Corpus.Defs.LieOrder` copies the order formulas `orderA` to `orderTits` and `lieOrderFormula`,
which are equal to the corpus ones by `rfl`, and `lieOrderNumerator`, `lieOrderDivisor` and `lieSylowExponent`,
which are indexed by the copied inductive type `StatedLieTag` and agree with the corpus ones through
`statedLieTagToCorpus`.
-/

namespace CFSGOutsideClean.Corpus.LieOrder

open CFSGOutsideClean.Corpus.Open (statedLieTagToCorpus)

theorem lieOrderFormula_eq :
    CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula =
      CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula := by
  funext d
  cases d <;> rfl

theorem lieOrderNumerator_eq (t : CFSGOutside.Corpus.Open.StatedLieTag) (n q : ℕ) :
    CFSGOutside.Corpus.ComponentClassification.CatLeaf.lieOrderNumerator t n q =
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator (statedLieTagToCorpus t) n q := by
  cases t <;> rfl

theorem lieOrderDivisor_eq (t : CFSGOutside.Corpus.Open.StatedLieTag) (n q : ℕ) :
    CFSGOutside.Corpus.ComponentClassification.CatLeaf.lieOrderDivisor t n q =
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor (statedLieTagToCorpus t) n q := by
  cases t <;> rfl

theorem lieSylowExponent_eq (t : CFSGOutside.Corpus.Open.StatedLieTag) (n : ℕ) :
    CFSGOutside.Corpus.ComponentClassification.CatLeaf.lieSylowExponent t n =
      CFSG.ComponentClassification.CatLeaf.lieSylowExponent (statedLieTagToCorpus t) n := by
  cases t <;> rfl

end CFSGOutsideClean.Corpus.LieOrder
