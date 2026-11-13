import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_16
import CFSGOutside.Corpus.Proposition116B
import CFSGOutsideClean.Corpus.Defs.Frobenius

/-! The corpus proves the statement that `CFSGOutside.Corpus.Proposition116B` assumes. The copied
`fixedPointSubgroup` is the corpus definition by `rfl` (`CFSGOutsideClean.Corpus.fixedPointSubgroup_eq`). -/

universe u v

instance CFSGOutsideClean.Corpus.proposition116B : CFSGOutside.Corpus.Proposition116B.{u, v} :=
  ⟨@CFSG.proposition_1_16_b⟩
