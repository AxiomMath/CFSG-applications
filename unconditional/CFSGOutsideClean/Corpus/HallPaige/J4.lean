import Certificates.Certificate4008
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Schreier.J4SOrder
import CFSGOutsideClean.Corpus.HallPaige.Defs.J4

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.J4` assumes. -/

instance CFSGOutsideClean.Corpus.hpJ4Bridge : CFSGOutside.Corpus.J4.Bridge :=
  ⟨CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv⟩

instance CFSGOutsideClean.Corpus.hpJ4Cover : CFSGOutside.Corpus.J4.Cover := by
  refine ⟨?_⟩
  rw [CFSGOutsideClean.Corpus.J4_pathElt_eq, CFSGOutsideClean.Corpus.J4_rootV_toVec_eq]
  exact Certificates.certificate4008

instance CFSGOutsideClean.Corpus.hpJ4Stab : CFSGOutside.Corpus.J4.Stab :=
  ⟨CFSG.Sporadic.J4Schreier.stabilizer_v_eq_Hj⟩
