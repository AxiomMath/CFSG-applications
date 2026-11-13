import CFSG.Open.StatedDefs
import CFSGOutside.Corpus.HallPaige.LieUnitary

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.LieUnitary` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Lie_StatedSU_eq :
    @CFSGOutside.Corpus.Lie.StatedSU = @CFSG.Open.StatedSU := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
