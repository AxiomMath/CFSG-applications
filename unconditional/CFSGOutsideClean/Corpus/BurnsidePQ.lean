import CFSG.CharacterTheory.Burnside
import CFSGOutside.Corpus.BurnsidePQ

/-! The corpus proves the statement that `CFSGOutside.Corpus.BurnsidePQ` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.burnsidePQ : CFSGOutside.Corpus.BurnsidePQ.{u} :=
  ⟨fun hp hq hpq hcard =>
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq hcard⟩
