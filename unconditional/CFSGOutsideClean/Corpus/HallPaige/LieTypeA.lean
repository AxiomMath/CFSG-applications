import CFSG.Adapters.LinearCatalog
import CFSGOutside.Corpus.HallPaige.LieTypeA

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieTypeA` assumes. -/

instance CFSGOutsideClean.Corpus.hpLieTypeATypeAEquiv : CFSGOutside.Corpus.Lie.TypeAEquiv :=
  ⟨fun r q _ hv => ⟨CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv⟩⟩
