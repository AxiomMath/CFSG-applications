import Mathlib

/-!
# Corpus input: Burnside's `p^a q^b` theorem

Statement of `CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow`, copied verbatim from
`CFSG/CharacterTheory/Burnside.lean` (line 12) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962.

The corpus theorem is universe polymorphic, so the class takes the universe as a parameter: a lemma about
`G : Type u` assumes `[BurnsidePQ.{u}]`. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/BurnsidePQ.lean`.
-/

universe u

namespace CFSGOutside.Corpus

/-- Burnside: a finite group of order `p ^ a * q ^ b` for primes `p ≠ q` is solvable. -/
class BurnsidePQ : Prop where
  finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow : ∀ {G : Type u} [Group G] [Fintype G]
    {p q a b : ℕ} (_hp : Nat.Prime p) (_hq : Nat.Prime q) (_hpq : p ≠ q)
    (_hcard : Fintype.card G = p ^ a * q ^ b), Group.IsSolvable G

end CFSGOutside.Corpus
