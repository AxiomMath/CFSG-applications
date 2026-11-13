import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import CFSGOutside.Corpus.IsSteinerTripleHexads
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.IsSteinerTripleHexads` assumes. -/

instance CFSGOutsideClean.Corpus.isSteinerTripleHexads : CFSGOutside.Corpus.IsSteinerTripleHexads :=
  ⟨CFSG.ComponentClassification.WittDesign.isSteinerTriple_hexads⟩
