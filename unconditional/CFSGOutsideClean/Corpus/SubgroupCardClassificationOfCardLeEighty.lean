import CFSG.Permutation.FiveTransitive
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-! The corpus proves the statement that `CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty`
assumes. -/

instance CFSGOutsideClean.Corpus.subgroupCardClassificationOfCardLeEighty :
    CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty :=
  ⟨CFSG.FiveTransitive.subgroup_card_classification_of_card_le_eighty⟩
