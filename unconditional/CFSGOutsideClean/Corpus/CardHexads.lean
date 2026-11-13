import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
import CFSGOutside.Corpus.CardHexads
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.CardHexads` assumes. -/

instance CFSGOutsideClean.Corpus.cardHexads : CFSGOutside.Corpus.CardHexads :=
  ⟨CFSG.ComponentClassification.WittDesign.card_hexads⟩
