import CFSG.Sporadic.Presentation.Co3
import CFSGOutside.Corpus.HallPaige.Co3

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Co3` assumes. -/

instance CFSGOutsideClean.Corpus.hpCo3FiniteCardLe : CFSGOutside.Corpus.Co3.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Co3.finite_card_le⟩
