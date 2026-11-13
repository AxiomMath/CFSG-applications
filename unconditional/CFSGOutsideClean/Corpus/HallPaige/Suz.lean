import CFSG.Sporadic.Presentation.Suz
import CFSGOutside.Corpus.HallPaige.Suz

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Suz` assumes. -/

instance CFSGOutsideClean.Corpus.hpSuzFiniteCardLe : CFSGOutside.Corpus.Suz.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Suz.finite_card_le⟩
