import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup
import CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutsideClean.Corpus.Defs.ElemThompson

/-! The corpus proves the statement that `CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup` assumes. The copied
`pRank` is matched to the corpus one by `CFSGOutsideClean.Corpus.pRank_eq`. -/

universe u

instance CFSGOutsideClean.Corpus.twoLePRankOfIsSimpleGroup : CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup.{u} :=
  ⟨fun hS => by
    rw [CFSGOutsideClean.Corpus.pRank_eq]
    exact CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup hS⟩
