import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: the automorphism group of the hexads has order 887040 and contains `M22` with index 2

Statement of `CFSG.ComponentClassification.WittDesign.card_hexadAut`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignWittAut.lean` (line 290) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `hexadAut` and `M22` the copies in
`CFSGOutside.Corpus.Defs.WittDesign`. The clean build provides the instance, in
`results_unconditional/CFSGOutsideClean/Corpus/CardHexadAut.lean`.
-/

namespace CFSGOutside.Corpus

open WittDesign

/-- `|hexadAut| = 887040` and `[hexadAut : M22] = 2`, as `card_hexadAut` states it. -/
class CardHexadAut : Prop where
  card_hexadAut : Nat.card hexadAut = 887040 ∧ M22.relIndex hexadAut = 2

end CFSGOutside.Corpus
