import CFSG.ClassicalGroups.McLaughlin.Centres
import CFSGOutside.Corpus.McLaughlinCentres
import CFSGOutsideClean.Corpus.Defs.McLaughlin

/-! The corpus proves the statement that `CFSGOutside.Corpus.McLaughlinCentres` assumes. -/

instance CFSGOutsideClean.Corpus.mcLaughlinCentres : CFSGOutside.Corpus.McLaughlinCentres :=
  ⟨by
    intro _ _ _ _ _ _ hK hn _ hgen hirr _ hv
    exact CFSG.ClassicalGroups.McLaughlin.isCentre_of_ne_zero hK hn hgen hirr hv⟩
