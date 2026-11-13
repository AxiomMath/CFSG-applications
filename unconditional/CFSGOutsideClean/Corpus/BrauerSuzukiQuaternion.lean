import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSGOutside.Corpus.BrauerSuzukiQuaternion

/-! The corpus proves the statement that `CFSGOutside.Corpus.BrauerSuzukiQuaternion` assumes. -/

instance CFSGOutsideClean.Corpus.brauerSuzukiQuaternion : CFSGOutside.Corpus.BrauerSuzukiQuaternion :=
  ⟨@CFSG.Quasithin.F6.false_of_sylow_quaternion⟩
