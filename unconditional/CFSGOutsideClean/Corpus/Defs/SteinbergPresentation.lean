import CFSG.Open.SteinbergPresentationMilestoneDefs
import CFSGOutside.Corpus.Defs.SteinbergPresentation

/-! The Steinberg relations copied into `CFSGOutside.Corpus.Defs.SteinbergPresentation` are the corpus
definition. -/

namespace CFSGOutsideClean.Corpus

theorem steinbergSLRels_eq (n : ℕ) (F : Type) [Field F] :
    CFSGOutside.Corpus.Open.steinbergSLRels n F = CFSG.Open.steinbergSLRels n F :=
  rfl

end CFSGOutsideClean.Corpus
