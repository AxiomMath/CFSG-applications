import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: the hexads form an `S(3,6,22)`

Statement of `CFSG.ComponentClassification.WittDesign.isSteinerTriple_hexads`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignM22Hexads.lean` (line 70) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with the corpus definitions it mentions replaced by their copies in
`CFSGOutside.Corpus.Defs.WittDesign`. The clean build provides the instance, in
`results_unconditional/CFSGOutsideClean/Corpus/IsSteinerTripleHexads.lean`.
-/

namespace CFSGOutside.Corpus

open WittDesign

/-- The 77 hexads form a Steiner system `S(3,6,22)`, as `isSteinerTriple_hexads` states it. -/
class IsSteinerTripleHexads : Prop where
  isSteinerTriple_hexads : IsSteinerTriple hexads

end CFSGOutside.Corpus
