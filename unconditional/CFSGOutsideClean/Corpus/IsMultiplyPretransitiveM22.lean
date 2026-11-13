import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
import CFSGOutside.Corpus.IsMultiplyPretransitiveM22
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.IsMultiplyPretransitiveM22` assumes. -/

instance CFSGOutsideClean.Corpus.isMultiplyPretransitiveM22 :
    CFSGOutside.Corpus.IsMultiplyPretransitiveM22 :=
  ⟨CFSG.ComponentClassification.WittDesign.isMultiplyPretransitive_M22⟩
