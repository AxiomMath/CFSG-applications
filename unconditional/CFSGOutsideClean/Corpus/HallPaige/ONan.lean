import CFSG.Sporadic.Presentation.ONan
import CFSGOutside.Corpus.HallPaige.ONan

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.ONan` assumes. -/

instance CFSGOutsideClean.Corpus.hpONanFiniteCardLe : CFSGOutside.Corpus.ONan.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.ONan.finite_card_le⟩
