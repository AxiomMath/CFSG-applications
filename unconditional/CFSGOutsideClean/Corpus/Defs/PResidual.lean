import CFSG.Quasithin.Background.A1cTransfer
import CFSGOutside.Corpus.Defs.PResidual

/-! The definition copied into `CFSGOutside.Corpus.Defs.PResidual` is the corpus definition. -/

namespace CFSGOutsideClean.Corpus

theorem pResidual_eq (p : ℕ) (X : Type*) [Group X] :
    CFSGOutside.Corpus.Quasithin.pResidual p X = CFSG.Quasithin.pResidual p X :=
  rfl

end CFSGOutsideClean.Corpus
