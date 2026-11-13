import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime
import CFSGOutsideClean.Corpus.Defs.ElemThompson

/-! The corpus proves the statement that `CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime`
assumes. The copied `IsSylowOf` is the corpus definition (`CFSGOutsideClean.Corpus.isSylowOf_iff`). -/

universe u

instance CFSGOutsideClean.Corpus.existsIsSylowOfNormalizedOfCoprime :
    CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{u} :=
  ⟨@CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime⟩
