import CFSG.Open.Defs
import CFSGOutside.Corpus.Defs.OddCore

/-! The definition copied into `CFSGOutside.Corpus.Defs.OddCore` is the corpus definition. -/

namespace CFSGOutsideClean.Corpus

theorem open_isQuasisimple_iff (G : Type*) [Group G] :
    CFSGOutside.Corpus.Open.IsQuasisimple G ↔ CFSG.Open.IsQuasisimple G :=
  Iff.rfl

end CFSGOutsideClean.Corpus
