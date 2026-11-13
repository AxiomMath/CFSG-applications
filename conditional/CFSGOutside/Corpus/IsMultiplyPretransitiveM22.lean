import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: `M22` is 3-transitive on 22 points

Statement of `CFSG.ComponentClassification.WittDesign.isMultiplyPretransitive_M22`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignM22Transitive.lean` (line 26) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `M22` the copy in `CFSGOutside.Corpus.Defs.WittDesign`. The clean build
provides the instance, in `results_unconditional/CFSGOutsideClean/Corpus/IsMultiplyPretransitiveM22.lean`.
-/

namespace CFSGOutside.Corpus

open WittDesign MulAction

/-- `M22` is 3-transitive on `Fin 22`, as `isMultiplyPretransitive_M22` states it. -/
class IsMultiplyPretransitiveM22 : Prop where
  isMultiplyPretransitive_M22 : IsMultiplyPretransitive M22 (Fin 22) 3

end CFSGOutside.Corpus
