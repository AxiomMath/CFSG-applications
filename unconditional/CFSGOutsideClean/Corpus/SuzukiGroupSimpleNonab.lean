import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
import CFSGOutside.Corpus.SuzukiGroupSimpleNonab

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiGroupSimpleNonab` assumes. -/

instance CFSGOutsideClean.Corpus.suzukiGroupSimpleNonab : CFSGOutside.Corpus.SuzukiGroupSimpleNonab :=
  ⟨by
    intro b hb k _ _ hk
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab hb hk⟩
