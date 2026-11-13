import CFSGOutside.Corpus.Defs.GGWeylInputs

/-!
# Corpus input: products of two reflections in a Weyl group

Statement of `CFSG.StandardType.ggSecFiveCoxProdInput_holds`
(`CFSG/LocalAnalysis/StandardType/GGSecFiveCoxProdHolds.lean`, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), which is `CFSG.StandardType.GGSecFiveCoxProdInput`, copied in
`CFSGOutside.Corpus.Defs.GGWeylInputs`.
-/

namespace CFSGOutside.Corpus

/-- In a Weyl group not of type `G₂`, the product of two reflections has order at most `4`. -/
class GGSecFiveCoxProd : Prop where
  ggSecFiveCoxProdInput_holds : StandardType.GGSecFiveCoxProdInput

end CFSGOutside.Corpus
