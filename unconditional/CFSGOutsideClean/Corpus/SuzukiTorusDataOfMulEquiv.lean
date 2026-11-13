import CFSG.GroupTheory.SuzukiPointTorus.Transport
import CFSGOutside.Corpus.SuzukiTorusDataOfMulEquiv
import CFSGOutsideClean.Corpus.Defs.SuzukiTorusData

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiTorusDataOfMulEquiv` assumes. -/

universe u v

instance CFSGOutsideClean.Corpus.suzukiTorusDataOfMulEquiv :
    CFSGOutside.Corpus.SuzukiTorusDataOfMulEquiv.{u, v} :=
  ⟨by
    intro X Y _ _ _ _ e q h
    exact (CFSGOutsideClean.Corpus.suzukiTorusData_iff _).2
      (CFSG.GroupTheory.SuzukiTorusData.of_mulEquiv e
        ((CFSGOutsideClean.Corpus.suzukiTorusData_iff _).1 h))⟩
