import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSGOutside.Corpus.CardStatedProjStatedSL
import CFSGOutsideClean.Corpus.Defs.ClassicalModel

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardStatedProjStatedSL` assumes. The copied
`StatedProj` and `StatedSL` are the corpus definitions by `rfl`. -/

instance CFSGOutsideClean.Corpus.cardStatedProjStatedSL : CFSGOutside.Corpus.CardStatedProjStatedSL :=
  ⟨fun hn => CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hn⟩
