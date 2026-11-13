import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSGOutside.Corpus.CardPsuThreeMulGcd
import CFSGOutsideClean.Corpus.Defs.ClassicalModel

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardPsuThreeMulGcd` assumes. The copied `StatedProj`
and `StatedSU` are the corpus definitions by `rfl`. -/

instance CFSGOutsideClean.Corpus.cardPsuThreeMulGcd : CFSGOutside.Corpus.CardPsuThreeMulGcd :=
  ⟨fun hp hf hK => CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd hp hf hK⟩
