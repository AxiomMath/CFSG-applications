import CFSGOutside.Corpus.Defs.SteinbergPresentation

/-!
# Corpus input: the Steinberg presentation of `SL_{m+1}(F)`

Statement of `CFSG.LieType.Steinberg.SL.exists_steinbergSLRels_equiv`
(`CFSG/LieType/Steinberg/Classical/SpecialLinearSteinberg.lean`, line 215, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), with `steinbergSLRels` the copy in `CFSGOutside.Corpus.Defs`.

For `m ≥ 2` and a finite field `F`, the group presented by the Steinberg relations is isomorphic to
`SL_{m+1}(F)`, with `x_ij(c) ↦ 1 + c E_ij`.
-/

namespace CFSGOutside.Corpus

/-- The Steinberg presentation of `SL_{m+1}(F)`, `m ≥ 2`, `F` finite, as
`exists_steinbergSLRels_equiv` states it. -/
class ExistsSteinbergSLRelsEquiv : Prop where
  exists_steinbergSLRels_equiv : ∀ {m : ℕ} {F : Type} [Field F] [Finite F], 2 ≤ m →
    ∃ φ : PresentedGroup (Open.steinbergSLRels (m + 1) F) ≃*
        Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      ∀ (i j : Fin (m + 1)) (c : F), i ≠ j →
        ((φ (PresentedGroup.of (i, j, c)) : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.transvection i j c

end CFSGOutside.Corpus
