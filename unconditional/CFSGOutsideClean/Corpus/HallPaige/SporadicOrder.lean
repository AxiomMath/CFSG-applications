import CFSG.Sporadic.Presentation.HeExact
import CFSG.Sporadic.Presentation.J3
import CFSGOutside.Corpus.HallPaige.SporadicOrder

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.SporadicOrder` assumes. -/

instance CFSGOutsideClean.Corpus.hpSporadicOrderBounds : CFSGOutside.Corpus.Bounds :=
  ⟨CFSG.Sporadic.Presentation.J3.finite_card_le, CFSG.Sporadic.Presentation.He.finite_card_le⟩
