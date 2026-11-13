import CFSG.Sporadic.Presentation.HN
import CFSGOutside.Corpus.HallPaige.HN

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.HN` assumes. -/

instance CFSGOutsideClean.Corpus.hpHNFiniteCardLe : CFSGOutside.Corpus.HN.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.HN.finite_card_le⟩
