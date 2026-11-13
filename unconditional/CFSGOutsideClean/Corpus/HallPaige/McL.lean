import CFSG.Sporadic.Presentation.McLExact
import CFSGOutside.Corpus.HallPaige.McL

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.McL` assumes. -/

instance CFSGOutsideClean.Corpus.hpMcLFiniteCardLe : CFSGOutside.Corpus.McL.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.McL.finite_card_le⟩
