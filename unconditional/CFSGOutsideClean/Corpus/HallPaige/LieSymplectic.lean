import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSGOutside.Corpus.HallPaige.LieSymplectic

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieSymplectic` assumes. -/

instance CFSGOutsideClean.Corpus.hpLieSymplecticSymplecticEquivs : CFSGOutside.Corpus.Lie.SymplecticEquivs :=
  ⟨CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj, CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj, CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj⟩
