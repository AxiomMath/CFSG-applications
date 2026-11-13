import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
import CFSGOutside.Corpus.M22LeHexadAut
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.M22LeHexadAut` assumes. -/

instance CFSGOutsideClean.Corpus.m22LeHexadAut : CFSGOutside.Corpus.M22LeHexadAut :=
  ⟨CFSG.ComponentClassification.WittDesign.M22_le_hexadAut⟩
