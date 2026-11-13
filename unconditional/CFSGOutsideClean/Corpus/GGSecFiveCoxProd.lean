import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxProdHolds
import CFSGOutside.Corpus.GGSecFiveCoxProd
import CFSGOutsideClean.Corpus.Defs.GGWeylInputs

/-! The corpus proves the statement that `CFSGOutside.Corpus.GGSecFiveCoxProd` assumes. -/

instance CFSGOutsideClean.Corpus.ggSecFiveCoxProd : CFSGOutside.Corpus.GGSecFiveCoxProd :=
  ⟨CFSGOutsideClean.Corpus.StandardType.ggSecFiveCoxProdInput_iff.mpr
    CFSG.StandardType.ggSecFiveCoxProdInput_holds⟩
