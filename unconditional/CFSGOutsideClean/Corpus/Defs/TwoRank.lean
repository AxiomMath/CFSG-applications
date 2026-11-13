import CFSG.Open.LocalVocabulary
import CFSGOutside.Corpus.Defs.TwoRank

/-! The definition copied into `CFSGOutside.Corpus.Defs.TwoRank` is the corpus definition. -/

theorem CFSGOutsideClean.Corpus.Open.twoRank_eq (G : Type*) [Group G] [Finite G] :
    CFSGOutside.Corpus.Open.twoRank G = CFSG.Open.twoRank G :=
  rfl
