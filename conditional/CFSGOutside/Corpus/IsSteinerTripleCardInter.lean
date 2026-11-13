import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: two blocks of an `S(3,6,22)` meet in 0 or 2 points

Statement of `CFSG.ComponentClassification.WittDesign.IsSteinerTriple.card_inter`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignSteiner3.lean` (line 110) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `IsSteinerTriple` the copy in
`CFSGOutside.Corpus.Defs.WittDesign`. The corpus theorem is universe polymorphic in the point type, so the class takes
its universe as a parameter. The clean build provides every instance, in
`results_unconditional/CFSGOutsideClean/Corpus/IsSteinerTripleCardInter.lean`.
-/

universe u

namespace CFSGOutside.Corpus

open WittDesign

/-- Two distinct blocks of an `S(3,6,22)` meet in 0 or 2 points, as `IsSteinerTriple.card_inter` states it. -/
class IsSteinerTripleCardInter : Prop where
  isSteinerTriple_card_inter : ∀ {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {𝓑 : Finset (Finset Ω)}
    (_h : IsSteinerTriple 𝓑) {B B' : Finset Ω} (_hB : B ∈ 𝓑) (_hB' : B' ∈ 𝓑) (_hne : B ≠ B'),
    (B ∩ B').card = 0 ∨ (B ∩ B').card = 2

end CFSGOutside.Corpus
