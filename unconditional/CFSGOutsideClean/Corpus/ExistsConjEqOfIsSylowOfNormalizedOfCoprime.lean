import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime
import CFSGOutsideClean.Corpus.Defs.ElemThompson

/-! The corpus proves the statement that `CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime`
assumes. The copied `IsSylowOf` is the corpus definition (`CFSGOutsideClean.Corpus.isSylowOf_iff`). -/

universe u

instance CFSGOutsideClean.Corpus.existsConjEqOfIsSylowOfNormalizedOfCoprime :
    CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{u} :=
  ⟨@CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime⟩
