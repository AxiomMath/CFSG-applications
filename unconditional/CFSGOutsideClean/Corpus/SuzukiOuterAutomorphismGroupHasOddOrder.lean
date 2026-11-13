import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
import CFSGOutside.Corpus.SuzukiOuterAutomorphismGroupHasOddOrder

/-! The corpus proves the statement that `CFSGOutside.Corpus.SuzukiOuterAutomorphismGroupHasOddOrder` assumes. -/

instance CFSGOutsideClean.Corpus.suzukiOuterAutomorphismGroupHasOddOrder :
    CFSGOutside.Corpus.SuzukiOuterAutomorphismGroupHasOddOrder :=
  ⟨fun ha hK =>
    CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order ha hK⟩
