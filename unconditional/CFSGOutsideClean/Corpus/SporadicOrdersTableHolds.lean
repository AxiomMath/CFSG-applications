import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
import CFSGOutside.Corpus.SporadicOrdersTableHolds
import CFSGOutsideClean.Corpus.Defs.SporadicOrder

/-! The corpus proves the statement that `CFSGOutside.Corpus.SporadicOrdersTableHolds` assumes. -/

instance CFSGOutsideClean.Corpus.sporadicOrdersTableHolds :
    CFSGOutside.Corpus.SporadicOrdersTableHolds :=
  ⟨CFSGOutsideClean.Corpus.SporadicOrder.sporadicOrdersTable_iff.2
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds⟩
