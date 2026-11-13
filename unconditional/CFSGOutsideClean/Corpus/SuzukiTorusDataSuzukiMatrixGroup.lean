import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsSzPointActionTorus
import CFSGOutside.Corpus.SuzukiTorusDataSuzukiMatrixGroup
import CFSGOutsideClean.Corpus.Defs.SuzukiTorusData

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiTorusDataSuzukiMatrixGroup` assumes. -/

instance CFSGOutsideClean.Corpus.suzukiTorusDataSuzukiMatrixGroup :
    CFSGOutside.Corpus.SuzukiTorusDataSuzukiMatrixGroup :=
  ⟨fun m hm =>
    (CFSGOutsideClean.Corpus.suzukiTorusData_iff _).2
      (CFSG.LocalAnalysis.UniquenessCase.UC22.suzukiTorusData_suzukiMatrixGroup m hm)⟩
