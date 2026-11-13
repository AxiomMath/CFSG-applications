import CFSG.Open.StatedDefs
import CFSGOutside.Corpus.HallPaige.LieOrth

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.LieOrth` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Lie_StatedOmega_eq :
    @CFSGOutside.Corpus.Lie.StatedOmega = @CFSG.Open.StatedOmega := by
  with_unfolding_all rfl

theorem Lie_StatedQuadOdd_eq :
    @CFSGOutside.Corpus.Lie.StatedQuadOdd = @CFSG.Open.StatedQuadOdd := by
  with_unfolding_all rfl

theorem Lie_StatedQuadPlus_eq :
    @CFSGOutside.Corpus.Lie.StatedQuadPlus = @CFSG.Open.StatedQuadPlus := by
  with_unfolding_all rfl

theorem Lie_StatedQuadMinus_eq :
    @CFSGOutside.Corpus.Lie.StatedQuadMinus = @CFSG.Open.StatedQuadMinus := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
