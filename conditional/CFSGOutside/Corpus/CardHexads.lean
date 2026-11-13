import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: there are 77 hexads

Statement of `CFSG.ComponentClassification.WittDesign.card_hexads`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignM22Hexads.lean` (line 51) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `hexads` the copy in `CFSGOutside.Corpus.Defs.WittDesign`. The clean
build provides the instance, in `results_unconditional/CFSGOutsideClean/Corpus/CardHexads.lean`.
-/

namespace CFSGOutside.Corpus

open WittDesign

/-- There are 77 hexads, as `card_hexads` states it. -/
class CardHexads : Prop where
  card_hexads : hexads.card = 77

end CFSGOutside.Corpus
