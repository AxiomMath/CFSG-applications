import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
import CFSGOutside.Corpus.IsSteinerTripleCardInter
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.IsSteinerTripleCardInter` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.isSteinerTripleCardInter :
    CFSGOutside.Corpus.IsSteinerTripleCardInter.{u} :=
  ⟨@fun _ _ _ _ h _ _ hB hB' hne =>
    CFSG.ComponentClassification.WittDesign.IsSteinerTriple.card_inter h hB hB' hne⟩
