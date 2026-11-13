import CFSG.Milestones.LR_rank_two_isomorphism_types
import CFSGOutside.Corpus.LrRankTwoIsomorphismTypes
import CFSGOutsideClean.Corpus.Defs.ClassicalModel
import CFSGOutsideClean.Corpus.Defs.TwoRank
import CFSGOutsideClean.Corpus.Defs.StatedM11

/-! The corpus proves the statement that `CFSGOutside.Corpus.LrRankTwoIsomorphismTypes` assumes. The copied
`StatedClassicalModel` is matched to the corpus one by `CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff`;
`twoRank` and `StatedM11` are the corpus definitions by `rfl`. -/

instance CFSGOutsideClean.Corpus.lrRankTwoIsomorphismTypes : CFSGOutside.Corpus.LrRankTwoIsomorphismTypes :=
  ⟨fun G _ _ _ hnonab hrank => by
    simp_rw [CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff]
    exact CFSG.Milestones.lr_rank_two_isomorphism_types G hnonab hrank⟩
