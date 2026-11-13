import CFSG.Walter.J1Props
import CFSGOutside.Corpus.J2Inverted
import CFSGOutsideClean.Corpus.Defs.Walter

/-! The corpus proves the statement that `CFSGOutside.Corpus.J2Inverted` assumes. The copied `walterJ1` is the
corpus definition (`CFSGOutsideClean.Corpus.Walter.walterJ1_eq`). -/

instance CFSGOutsideClean.Corpus.j2Inverted : CFSGOutside.Corpus.J2Inverted :=
  ⟨fun hp2 P => CFSG.Walter.J1Props.J2_inverted hp2 P⟩
