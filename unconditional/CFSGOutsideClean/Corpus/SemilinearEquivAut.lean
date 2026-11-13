import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.CharacterTheory.Semidihedral.SemilinearLayerModel
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutsideClean.Corpus.Defs.PGammaL2
import CFSGOutsideClean.Corpus.Defs.OddCoreDihedral

/-! The corpus proves the statement that `CFSGOutside.Corpus.SemilinearEquivAut` assumes. The copied `PGammaL2`
and `PSL2` are the corpus definitions by `rfl`. -/

universe u

instance CFSGOutsideClean.Corpus.semilinearEquivAut : CFSGOutside.Corpus.SemilinearEquivAut.{u} :=
  ⟨fun K _ _ => ⟨CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearEquivAut K,
    CFSG.Semidihedral.SemilinearLayerModel.semilinearEquivAut_symm_conj K⟩⟩
