import CFSG.LocalAnalysis.StandardType.ZS.UseInputHolds
import CFSGOutside.Corpus.ZSUseInput
import CFSGOutsideClean.Corpus.Defs.ZSReflectionGroups

/-! The corpus proves the statement that `CFSGOutside.Corpus.ZSUseInput` assumes. -/

instance CFSGOutsideClean.Corpus.zsUseInput : CFSGOutside.Corpus.ZSUseInput :=
  ⟨CFSGOutsideClean.Corpus.StandardType.useInput_of_corpus CFSG.StandardType.ZS.useInput_holds⟩
