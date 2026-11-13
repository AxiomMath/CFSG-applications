import CFSGOutside.Corpus.Defs.SuzukiTorusData

/-!
# Corpus input: the Suzuki point/torus axioms transport along isomorphisms

Statement of `CFSG.GroupTheory.SuzukiTorusData.of_mulEquiv`, copied verbatim from
`CFSG/GroupTheory/SuzukiPointTorus/Transport.lean` (line 223) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with
`SuzukiTorusData` the copy in `CFSGOutside.Corpus`.

The corpus theorem is universe polymorphic, so the class takes both universes as parameters.
-/

universe u v

namespace CFSGOutside.Corpus

/-- If `X ≅ Y` are finite groups and `Y` satisfies the point/torus axioms for `q`, so does `X`. -/
class SuzukiTorusDataOfMulEquiv : Prop where
  of_mulEquiv : ∀ {X : Type u} {Y : Type v} [Group X] [Finite X] [Group Y] [Finite Y] (_e : X ≃* Y)
    {q : ℕ} (_h : SuzukiTorusData Y q), SuzukiTorusData X q

end CFSGOutside.Corpus
