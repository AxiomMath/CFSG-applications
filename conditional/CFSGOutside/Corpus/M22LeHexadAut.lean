import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: `M22` preserves the hexads

Statement of `CFSG.ComponentClassification.WittDesign.M22_le_hexadAut`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignWittAut.lean` (line 74) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `M22` and `hexadAut` the copies in
`CFSGOutside.Corpus.Defs.WittDesign`. The clean build provides the instance, in
`results_unconditional/CFSGOutsideClean/Corpus/M22LeHexadAut.lean`.
-/

namespace CFSGOutside.Corpus

open WittDesign

/-- `M22 ≤ hexadAut`, as `M22_le_hexadAut` states it. -/
class M22LeHexadAut : Prop where
  M22_le_hexadAut : M22 ≤ hexadAut

end CFSGOutside.Corpus
