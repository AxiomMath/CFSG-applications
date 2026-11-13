import CFSG.RankThree.Theta.SignalizerCompleteness
import CFSGOutside.Corpus.SolvableSignalizerDatumComplete
import CFSGOutsideClean.Corpus.Defs.SolvableSignalizerDatum

/-! The corpus proves the statement that `CFSGOutside.Corpus.SolvableSignalizerDatumComplete` assumes. -/

universe u v

instance CFSGOutsideClean.Corpus.solvableSignalizerDatumComplete :
    CFSGOutside.Corpus.SolvableSignalizerDatumComplete.{u, v} :=
  ⟨fun hd h3 => CFSG.RankThree.Theta.solvable_signalizer_datum_complete
    ((CFSGOutsideClean.Corpus.isSolvableSignalizerDatum_iff _ _ _ _ _).1 hd) h3⟩
