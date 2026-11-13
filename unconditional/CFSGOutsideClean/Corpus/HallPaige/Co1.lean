import CFSG.Sporadic.Bridge.Co1Surj
import CFSG.Sporadic.Co1.Module.Orbits
import CFSG.Sporadic.Co1.Module.PairsCheck
import CFSGOutside.Corpus.HallPaige.Co1

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Co1` assumes. -/

instance CFSGOutsideClean.Corpus.hpCo1Orbits : CFSGOutside.Corpus.Co1.Orbits :=
  ⟨CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv, CFSG.Sporadic.Co1.Module.co1_exists_unique_orbit, CFSG.Sporadic.Co1.Module.Pairs.cls_trans⟩
