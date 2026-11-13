import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.Co1.Module.OrbitsBase
import CFSG.Sporadic.Co1.Module.PairsCheckBase
import CFSGOutside.Corpus.HallPaige.Co1

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.Co1` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Co1_asciiWhitespace_eq :
    @CFSGOutside.Corpus.Co1.asciiWhitespace = @CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  with_unfolding_all rfl

theorem Co1_decode_eq :
    @CFSGOutside.Corpus.Co1.decode = @CFSG.Blueprint.NativeSporadic.decode := by
  with_unfolding_all rfl

theorem Co1_seedMonoid_eq :
    @CFSGOutside.Corpus.Co1.seedMonoid = @CFSG.Blueprint.NativeSporadic.seedMonoid := by
  with_unfolding_all rfl

theorem Co1_Co1Seed1_eq :
    @CFSGOutside.Corpus.Co1.Co1Seed1 = @CFSG.Blueprint.NativeSporadic.Co1Seed1 := by
  with_unfolding_all rfl

theorem Co1_Co1Seed2_eq :
    @CFSGOutside.Corpus.Co1.Co1Seed2 = @CFSG.Blueprint.NativeSporadic.Co1Seed2 := by
  with_unfolding_all rfl

theorem Co1_Co1_eq :
    @CFSGOutside.Corpus.Co1.Co1 = @CFSG.Blueprint.NativeSporadic.Co1 := by
  with_unfolding_all rfl

theorem Co1_Vec24_eq :
    @CFSGOutside.Corpus.Co1.Vec24 = @CFSG.Sporadic.Co1.Module.Vec24 := by
  with_unfolding_all rfl

theorem Co1_v₂_eq :
    @CFSGOutside.Corpus.Co1.v₂ = @CFSG.Sporadic.Co1.Module.v₂ := by
  with_unfolding_all rfl

theorem Co1_v₃_eq :
    @CFSGOutside.Corpus.Co1.v₃ = @CFSG.Sporadic.Co1.Module.v₃ := by
  with_unfolding_all rfl

theorem Co1_v₄_eq :
    @CFSGOutside.Corpus.Co1.v₄ = @CFSG.Sporadic.Co1.Module.v₄ := by
  with_unfolding_all rfl

theorem Co1_reps_eq :
    @CFSGOutside.Corpus.Co1.reps = @CFSG.Sporadic.Co1.Module.reps := by
  with_unfolding_all rfl

theorem Co1_co1Act_eq :
    @CFSGOutside.Corpus.Co1.co1Act = @CFSG.Sporadic.Co1.Module.co1Act := by
  with_unfolding_all rfl

theorem Co1_tyOrbC_eq :
    @CFSGOutside.Corpus.Co1.tyOrbC = @CFSG.Sporadic.Co1.Module.Pairs.tyOrbC := by
  with_unfolding_all rfl

theorem Co1_cls_eq :
    @CFSGOutside.Corpus.Co1.cls = @CFSG.Sporadic.Co1.Module.Pairs.cls := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
