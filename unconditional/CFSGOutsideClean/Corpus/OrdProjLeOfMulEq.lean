import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar
import CFSGOutside.Corpus.OrdProjLeOfMulEq
import CFSGOutsideClean.Corpus.Defs.LieOrder

/-! The corpus proves the statement that `CFSGOutside.Corpus.OrdProjLeOfMulEq` assumes. -/

open CFSGOutsideClean.Corpus.LieOrder CFSGOutsideClean.Corpus.Open

instance CFSGOutsideClean.Corpus.ordProjLeOfMulEq : CFSGOutside.Corpus.OrdProjLeOfMulEq :=
  ⟨fun {t n p f M} hadm hp2 hM {s} hs hs2 hsp => by
    rw [lieSylowExponent_eq]
    refine CFSG.ComponentClassification.GS82PumpInputs.OddChar.ordProj_le_of_mul_eq
      ((statedLieAdmissible_iff t n p f).1 hadm) hp2 ?_ hs hs2 hsp
    rw [← lieOrderDivisor_eq, ← lieOrderNumerator_eq]
    exact hM⟩
