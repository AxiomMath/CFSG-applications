import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2PGL
import CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso

/-! The corpus proves the statement that `CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.uc22s2112r34PglTameCasesIso :
    CFSGOutside.Corpus.Uc22s2112r34PglTameCasesIso.{u} :=
  ⟨@CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s2112r34_pgl_tame_cases_iso⟩
