import CFSG.Sporadic.Presentation.Co2
import CFSGOutside.Corpus.HallPaige.Co2

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Co2` assumes. -/

instance CFSGOutsideClean.Corpus.hpCo2FiniteCardLe : CFSGOutside.Corpus.Co2.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Co2.finite_card_le⟩
