import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut
import CFSGOutside.Corpus.CardHexadAut
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardHexadAut` assumes. -/

instance CFSGOutsideClean.Corpus.cardHexadAut : CFSGOutside.Corpus.CardHexadAut :=
  ⟨CFSG.ComponentClassification.WittDesign.card_hexadAut⟩
