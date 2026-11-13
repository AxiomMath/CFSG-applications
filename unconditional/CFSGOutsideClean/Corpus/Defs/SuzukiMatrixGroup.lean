import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import CFSGOutside.Corpus.Defs.SuzukiMatrixGroup

/-! The Suzuki matrix group copied into `CFSGOutside.Corpus.Defs.SuzukiMatrixGroup` is the corpus one. -/

namespace CFSGOutsideClean.Corpus

theorem suzukiMatrixGeneratorSet_eq (m : ℕ) :
    CFSGOutside.Corpus.SuzukiMatrixGeneratorSet m =
      CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGeneratorSet m :=
  rfl

theorem suzukiMatrixSubgroup_eq (m : ℕ) :
    CFSGOutside.Corpus.SuzukiMatrixSubgroup m = CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixSubgroup m :=
  rfl

theorem suzukiMatrixGroup_eq (m : ℕ) :
    CFSGOutside.Corpus.SuzukiMatrixGroup m = CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
  rfl

end CFSGOutsideClean.Corpus
