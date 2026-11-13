import CFSG.Sporadic.Presentation.Fi22Exact
import CFSGOutside.Corpus.HallPaige.Fi22

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Fi22` assumes. -/

instance CFSGOutsideClean.Corpus.hpFi22FiniteCardLe : CFSGOutside.Corpus.Fi22.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Fi22.finite_card_le⟩
