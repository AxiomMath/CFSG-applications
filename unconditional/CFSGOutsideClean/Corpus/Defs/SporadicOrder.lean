import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSGOutside.Corpus.Defs.SporadicOrder

/-! The copied sporadic order table is the corpus one. -/

namespace CFSGOutsideClean.Corpus.SporadicOrder

theorem sporOrd_eq :
    CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.sporOrd =
      CFSG.HardMathSupport.Solomon.Coordinator.sporOrd := by
  funext s
  cases s <;> rfl

theorem sporadicOrdersTable_iff :
    CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable ↔
      CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable := by
  unfold CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable
    CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable
  rw [sporOrd_eq]

end CFSGOutsideClean.Corpus.SporadicOrder
