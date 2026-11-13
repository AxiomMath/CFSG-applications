import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Corpus input: a nonabelian simple group has 2-rank at least two

Statement of `CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup`, copied verbatim from
`CFSG/LieType/Chevalley/CLSEvenE6GraphInvolutionFourGroup.lean` (line 36) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `pRank` is the copy of `CFSG.pRank` in `CFSGOutside.Corpus.Defs`.
The class takes the universe of `S` as a parameter.
-/

namespace CFSGOutside.Corpus

/-- A finite nonabelian simple group has 2-rank at least 2, as
`CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup` states it. -/
class TwoLePRankOfIsSimpleGroup.{u} : Prop where
  two_le_pRank_of_isSimpleGroup : ∀ {S : Type u} [Group S] [Finite S] [IsSimpleGroup S]
    (_hS : ∃ a b : S, a * b ≠ b * a), 2 ≤ pRank 2 S

end CFSGOutside.Corpus
