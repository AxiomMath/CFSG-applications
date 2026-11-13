import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSGOutside.Corpus.GGSecFiveRootRefl
import CFSGOutsideClean.Corpus.Defs.GGWeylInputs

/-! The corpus proves the statement that `CFSGOutside.Corpus.GGSecFiveRootRefl` assumes. -/

instance CFSGOutsideClean.Corpus.ggSecFiveRootRefl : CFSGOutside.Corpus.GGSecFiveRootRefl :=
  ⟨CFSGOutsideClean.Corpus.StandardType.ggSecFiveRootReflInput_iff.mpr
    CFSG.StandardType.SecFiveRootRefl.ggSecFiveRootReflInput_holds⟩
