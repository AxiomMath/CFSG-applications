import CFSG.Milestones.FAM_sporadic_converse
import CFSGOutside.Corpus.HallPaige.SporadicSimple

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.SporadicSimple` assumes. -/

instance CFSGOutsideClean.Corpus.hpSporadicSimpleSimple : CFSGOutside.Corpus.Simple :=
  ⟨CFSG.Milestones.fam_sporadic_converse_tauCeti⟩
