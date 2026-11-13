import CFSGOutside.Corpus.Defs.ClassicalModel

/-!
# Corpus input: the order of `PSU(3, q)`

Statement of `CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd`, copied verbatim from
`CFSG/Timmesfeld/Orders/ClassicalUnitaryThree.lean` (line 11) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `StatedProj` and `StatedSU` are the copies in
`CFSGOutside.Corpus.Defs.ClassicalModel`.
-/

namespace CFSGOutside.Corpus

open Open

/-- `|PSU(3, q)| · gcd(3, q + 1) = q³ (q² - 1)(q³ + 1)`, as `card_psu_three_mul_gcd` states it. -/
class CardPsuThreeMulGcd : Prop where
  card_psu_three_mul_gcd : ∀ {K : Type} [Field K] {p f : ℕ} (_hp : p.Prime) (_hf : 1 ≤ f)
    (_hK : Nat.card K = (p ^ f) ^ 2),
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))

end CFSGOutside.Corpus
