import CFSG.Sporadic.Presentation.RuExact
import CFSGOutside.Corpus.HallPaige.Ru

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Ru` assumes. -/

instance CFSGOutsideClean.Corpus.hpRuFiniteCardLe : CFSGOutside.Corpus.Ru.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Ru.finite_card_le⟩
