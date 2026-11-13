import CFSGOutside.Corpus.Defs.Suzuki

/-!
# Corpus input: involution centralizers in `Sz(q)`

Statement of `CFSG.RankThree.centralizer_eq_sylow`, copied verbatim from
`CFSG/RankThree/SteinbergR3ESuzukiInvolutionCentralizers.lean` (line 113) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `suzukiGroup` the copy in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus

/-- In `Sz(q)` the centralizer of an involution is the Sylow `2`-subgroup containing it. -/
class SuzukiCentralizerEqSylow : Prop where
  centralizer_eq_sylow : ∀ {a : ℕ} {K : Type} [Field K] [Finite K] (_hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : suzukiGroup a K} (_hz : orderOf z = 2) (Q : Sylow 2 (suzukiGroup a K)) (_hzQ : z ∈ Q),
    Subgroup.centralizer {z} = Q

end CFSGOutside.Corpus
