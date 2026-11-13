import CFSGOutside.Corpus.Defs.GGWeylInputs

/-!
# Corpus input: reflections in a Weyl automizer are root reflections

Statement of `CFSG.StandardType.SecFiveRootRefl.ggSecFiveRootReflInput_holds`
(`CFSG/LocalAnalysis/StandardType/GGSecFiveRootRefl.lean`, line 588, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), which is `CFSG.StandardType.GGSecFiveRootReflInput`, copied in
`CFSGOutside.Corpus.Defs.GGWeylInputs`.
-/

namespace CFSGOutside.Corpus

/-- Every reflection in a Weyl automizer (not of type `G₂`) is a conjugate of a simple reflection. -/
class GGSecFiveRootRefl : Prop where
  ggSecFiveRootReflInput_holds : StandardType.GGSecFiveRootReflInput

end CFSGOutside.Corpus
