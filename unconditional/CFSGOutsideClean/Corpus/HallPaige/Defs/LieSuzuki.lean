import CFSG.Blueprint.Catalog
import CFSG.LieType.Ree.SuzukiLocalData
import CFSGOutside.Corpus.HallPaige.LieSuzuki

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.LieSuzuki` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Lie_suzukiN_eq :
    @CFSGOutside.Corpus.Lie.suzukiN = @CFSG.Blueprint.suzukiN := by
  with_unfolding_all rfl

theorem Lie_suzukiS_eq :
    @CFSGOutside.Corpus.Lie.suzukiS = @CFSG.Blueprint.suzukiS := by
  with_unfolding_all rfl

theorem Lie_suzukiD_eq :
    @CFSGOutside.Corpus.Lie.suzukiD = @CFSG.Blueprint.suzukiD := by
  with_unfolding_all rfl

theorem Lie_suzukiW_eq :
    @CFSGOutside.Corpus.Lie.suzukiW = @CFSG.Blueprint.suzukiW := by
  with_unfolding_all rfl

theorem Lie_suzukiGroup_eq :
    @CFSGOutside.Corpus.Lie.suzukiGroup = @CFSG.Blueprint.suzukiGroup := by
  with_unfolding_all rfl

theorem Lie_SuzukiModel_eq :
    @CFSGOutside.Corpus.Lie.SuzukiModel = @CFSG.Blueprint.SuzukiModel := by
  with_unfolding_all rfl

theorem Lie_suzukiLine_eq :
    @CFSGOutside.Corpus.Lie.suzukiLine = @CFSG.LieType.Ree.suzukiLine := by
  with_unfolding_all rfl

theorem Lie_suzukiInfty_eq :
    @CFSGOutside.Corpus.Lie.suzukiInfty = @CFSG.LieType.Ree.suzukiInfty := by
  with_unfolding_all rfl

theorem Lie_suzukiOmega_eq :
    @CFSGOutside.Corpus.Lie.suzukiOmega = @CFSG.LieType.Ree.suzukiOmega := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
