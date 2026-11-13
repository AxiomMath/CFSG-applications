import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSGOutside.Corpus.LieOrderBridgeHolds
import CFSGOutsideClean.Corpus.Defs.LieOrder

/-! The corpus proves the statement that `CFSGOutside.Corpus.LieOrderBridgeHolds` assumes. -/

instance CFSGOutsideClean.Corpus.lieOrderBridgeHolds : CFSGOutside.Corpus.LieOrderBridgeHolds :=
  ⟨fun idx G _ _ h => by
    rw [CFSGOutsideClean.Corpus.LieOrder.lieOrderFormula_eq]
    exact CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds idx G h⟩
