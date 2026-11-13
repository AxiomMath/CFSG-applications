import CFSG.ClassicalGroups.Alternating.Generation
import CFSGOutside.Corpus.AlternatingTransvectionGeneration
import CFSGOutsideClean.Corpus.Defs.SymplecticIsometry

/-! The corpus proves the statement that `CFSGOutside.Corpus.AlternatingTransvectionGeneration` assumes. -/

instance CFSGOutsideClean.Corpus.alternatingTransvectionGeneration :
    CFSGOutside.Corpus.AlternatingTransvectionGeneration :=
  ⟨fun hB hBn => CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hB hBn⟩
