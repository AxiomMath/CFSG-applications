import CFSG.Permutation.FiveTransitive.SmallSupportGeneric
import CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix

/-! The corpus proves the statement that `CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix`
assumes. -/

instance CFSGOutsideClean.Corpus.alternatingGroupLeOfNontrivialSupportLeSix :
    CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix :=
  ⟨CFSG.FiveTransitive.SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six⟩
