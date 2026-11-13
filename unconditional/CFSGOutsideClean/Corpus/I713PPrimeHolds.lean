import CFSG.HardMathSupport.Solomon.Coordinator.I713
import CFSGOutside.Corpus.I713PPrimeHolds
import CFSGOutsideClean.Corpus.Defs.OpenVocabulary

/-! The corpus proves the statement that `CFSGOutside.Corpus.I713PPrimeHolds` assumes. The copied
`I_7_13_1_pPrime` is the corpus definition (`CFSGOutsideClean.Corpus.i_7_13_1_pPrime_iff`). -/

instance CFSGOutsideClean.Corpus.i713PPrimeHolds : CFSGOutside.Corpus.I713PPrimeHolds :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds⟩
