import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittUnique
import CFSGOutside.Corpus.SteinerTripleIso
import CFSGOutsideClean.Corpus.Defs.WittDesign

/-! The corpus proves the statement that `CFSGOutside.Corpus.SteinerTripleIso` assumes. -/

universe u u'

instance CFSGOutsideClean.Corpus.steinerTripleIso : CFSGOutside.Corpus.SteinerTripleIso.{u, u'} :=
  ⟨fun h h' => CFSG.ComponentClassification.WittDesign.steinerTriple_iso h h'⟩
