import CFSGOutside.Corpus.Defs.PGammaL2

/-!
# Corpus input: `Aut(PSL(2,K)) ≅ PΓL(2,K)`

The corpus defines `CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K : PGammaL2 K ≃*
MulAut (PSL2 K)` (`CFSG/LocalAnalysis/ComponentClassification/CatalogueSchreierLinearTwoAllFields.lean` line 68) and
proves `CFSG.Semidihedral.SemilinearLayerModel.semilinearEquivAut_symm_conj`
(`CFSG/CharacterTheory/Semidihedral/SemilinearLayerModel.lean` line 89): it sends the inner automorphism `conj x`
to `inl (toPGL x)`, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. The class packages the two: such an isomorphism exists. `PGammaL2` and
`PSL2` are the copies in `CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

open GorensteinWalter

/-- `PΓL(2,K)` is the automorphism group of `PSL(2,K)`, compatibly with inner automorphisms. -/
class SemilinearEquivAut.{u} : Prop where
  semilinearEquivAut : ∀ (K : Type u) [Field K] [Finite K],
    ∃ e : PGammaL2 K ≃* MulAut (PSL2 K), ∀ x : PSL2 K,
      e.symm (MulAut.conj x) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x)

end CFSGOutside.Corpus
