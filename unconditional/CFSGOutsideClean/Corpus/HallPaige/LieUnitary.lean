import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSGOutside.Corpus.HallPaige.LieUnitary

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.LieUnitary` assumes. -/

instance CFSGOutsideClean.Corpus.hpLieUnitaryUnitaryEquiv : CFSGOutside.Corpus.Lie.UnitaryEquiv :=
  ⟨fun r q hv => ⟨CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv⟩⟩
