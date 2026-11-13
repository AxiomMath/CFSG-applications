import CFSGOutside.Corpus.Defs.ClassicalModel

/-!
# Corpus input: the order of `PSL(n, q)`

Statement of `CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL`, copied verbatim from
`CFSG/Timmesfeld/Orders/ClassicalLinear.lean` (line 20) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `StatedProj` and `StatedSL` are the copies in
`CFSGOutside.Corpus.Defs.ClassicalModel`.
-/

namespace CFSGOutside.Corpus

open Open

/-- `|PSL(n, K)| = q^(n(n-1)/2) ∏_{j=2}^n (q^j - 1) / gcd(n, q - 1)`, as `card_statedProj_statedSL` states it. -/
class CardStatedProjStatedSL : Prop where
  card_statedProj_statedSL : ∀ {K : Type} [Field K] [Finite K] {n : ℕ} (_hn : 1 ≤ n),
    Nat.card (StatedProj (StatedSL n K)) =
      Nat.card K ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1)) /
        Nat.gcd n (Nat.card K - 1)

end CFSGOutside.Corpus
