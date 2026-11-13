import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.M24Surj
import CFSGOutside.Corpus.HallPaige.Mathieu

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Mathieu` assumes. -/

instance CFSGOutsideClean.Corpus.hpMathieuBridges : CFSGOutside.Corpus.Mathieu.Bridges :=
  ⟨CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv, CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv, CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv, CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv, CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv⟩
