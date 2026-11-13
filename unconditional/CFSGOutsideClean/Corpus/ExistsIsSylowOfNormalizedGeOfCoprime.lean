import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime
import CFSGOutsideClean.Corpus.Defs.ElemThompson

/-! The corpus proves the statement that `CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime`
assumes. The copied `IsSylowOf` is the corpus definition (`CFSGOutsideClean.Corpus.isSylowOf_iff`). -/

universe u

instance CFSGOutsideClean.Corpus.existsIsSylowOfNormalizedGeOfCoprime :
    CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{u} :=
  ⟨@CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_coprime⟩
