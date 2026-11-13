import CFSGOutside.Corpus.Defs.WittDesign

/-!
# Corpus input: uniqueness of the Steiner system `S(3,6,22)`

Statement of `CFSG.ComponentClassification.WittDesign.steinerTriple_iso`, copied verbatim from
`CFSG/LocalAnalysis/ComponentClassification/WittDesignWittUnique.lean` (line 245) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with `IsSteinerTriple` the copy in `CFSGOutside.Corpus.Defs.WittDesign`.

Witt: any two Steiner systems `S(3,6,22)` are isomorphic, by a bijection of the points that maps blocks onto
blocks. The corpus theorem is universe polymorphic (`Ω Ω' : Type*`), so the class takes the universes of the
two point types as parameters. The clean build provides every instance, in
`results_unconditional/CFSGOutsideClean/Corpus/SteinerTripleIso.lean`.
-/

universe u u'

namespace CFSGOutside.Corpus

open WittDesign

/-- Witt's uniqueness of `S(3,6,22)`, as `steinerTriple_iso` states it. -/
class SteinerTripleIso : Prop where
  steinerTriple_iso : ∀ {Ω : Type u} {Ω' : Type u'} [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝓑 : Finset (Finset Ω)} {𝓑' : Finset (Finset Ω')} (_h : IsSteinerTriple 𝓑)
    (_h' : IsSteinerTriple 𝓑'),
    ∃ e : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝓑 ↔ B.map e.toEmbedding ∈ 𝓑'

end CFSGOutside.Corpus
