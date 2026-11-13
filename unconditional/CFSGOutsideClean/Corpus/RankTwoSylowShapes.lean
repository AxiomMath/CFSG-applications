import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
import CFSGOutside.Corpus.RankTwoSylowShapes
import CFSGOutsideClean.Corpus.Defs.ClassicalModel
import CFSGOutsideClean.Corpus.Defs.TwoRank
import CFSGOutsideClean.Corpus.Defs.TwoGroupShapes

/-! The corpus proves the statement that `CFSGOutside.Corpus.RankTwoSylowShapes` assumes. The copied
`StatedClassicalModel` is matched to the corpus one by `CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff`. -/

instance CFSGOutsideClean.Corpus.rankTwoSylowShapes : CFSGOutside.Corpus.RankTwoSylowShapes :=
  ⟨fun hnonab hrank S => by
    rcases CFSG.RankTwoShapes.rank_two_sylow_shapes hnonab hrank S with h | h | h | ⟨H, _, U, hH, e⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨H, inferInstance, U,
        (CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff H .PSU 3 2 2).2 hH, e⟩))⟩
