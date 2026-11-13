import CFSG.Sporadic.Presentation.Fi24PrimeExact
import CFSGOutside.Corpus.HallPaige.Fi24Prime

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Fi24Prime` assumes. -/

instance CFSGOutsideClean.Corpus.hpFi24PrimeFiniteCardLe : CFSGOutside.Corpus.Fi24Prime.FiniteCardLe :=
  ⟨CFSG.Sporadic.Presentation.Fi24Prime.finite_card_le_exact⟩
