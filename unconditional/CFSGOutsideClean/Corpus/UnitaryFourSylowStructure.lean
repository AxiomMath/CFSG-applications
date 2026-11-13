import CFSG.LocalAnalysis.LyonsUnitaryFour.Local
import CFSGOutside.Corpus.UnitaryFourSylowStructure
import CFSGOutsideClean.Corpus.Defs.ClassicalModel

/-! The corpus proves the statement that `CFSGOutside.Corpus.UnitaryFourSylowStructure` assumes. The copied
`StatedClassicalModel` is matched to the corpus one by `CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff`. -/

instance CFSGOutsideClean.Corpus.unitaryFourSylowStructure : CFSGOutside.Corpus.UnitaryFourSylowStructure :=
  ⟨fun {_} _ {T} _ hT S U hSU =>
    CFSG.LyonsUnitaryFour.unitary_four_sylow_structure
      ((CFSGOutsideClean.Corpus.Open.statedClassicalModel_iff T .PSU 3 2 2).1 hT) S U hSU⟩
