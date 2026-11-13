import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutOrder8
import CFSGOutside.Corpus.Order8Nonabelian

/-! The corpus proves the statement that `CFSGOutside.Corpus.Order8Nonabelian` assumes. -/

instance CFSGOutsideClean.Corpus.order8Nonabelian : CFSGOutside.Corpus.Order8Nonabelian :=
  ⟨@CFSG.OddStandard.SmallF3.HarrisU33.Outside.order8_nonabelian⟩
