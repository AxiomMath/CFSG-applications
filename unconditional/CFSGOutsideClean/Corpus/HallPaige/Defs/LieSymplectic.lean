import CFSG.Open.StatedDefs
import CFSGOutside.Corpus.HallPaige.LieSymplectic

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.LieSymplectic` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Lie_StatedScalars_eq :
    @CFSGOutside.Corpus.Lie.StatedScalars = @CFSG.Open.StatedScalars := by
  with_unfolding_all rfl

theorem Lie_StatedProj_eq :
    @CFSGOutside.Corpus.Lie.StatedProj = @CFSG.Open.StatedProj := by
  with_unfolding_all rfl

theorem Lie_StatedSp_eq :
    @CFSGOutside.Corpus.Lie.StatedSp = @CFSG.Open.StatedSp := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
