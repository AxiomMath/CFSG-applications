import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
import CFSG.Sporadic.Schreier.TitsCert
import CFSG.Sporadic.Schreier.TitsStab
import Certificates.Kernel.Misc.Tits.Text
import CFSGOutside.Corpus.HallPaige.Tits
import CFSGOutsideClean.Corpus.HallPaige.Defs.Tits

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Tits` assumes. -/

attribute [local semireducible] CFSGOutside.Corpus.Tits.permOfArr CFSGOutside.Corpus.Tits.titsArr1755
  CFSG.Monster.B.Co2.permOfArr CFSG.Sporadic.Schreier.Tits.titsArr1755

namespace CFSGOutsideClean.Corpus

open CFSGOutside.Corpus.Tits

set_option maxRecDepth 100000 in -- the copied and the corpus permutation models are compared by unfolding
instance hpTitsTheorems : CFSGOutside.Corpus.Tits.Theorems where
  nonempty_mulEquiv_titsD_cat hv := by
    rw [Tits_titsD_eq]
    exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
  titsH_eq_stab := by
    rw [Tits_titsH_eq]
    exact CFSG.Sporadic.Schreier.Tits.titsH_eq_stab
  titsT_mem_titsD {i} hi := by
    rw [Tits_titsD_eq, show titsT i = CFSG.Sporadic.Schreier.Tits.titsT i from congrFun Tits_titsT_eq i]
    exact CFSG.Sporadic.Schreier.Tits.titsT_mem_titsD hi
  titsT_rep {i} hi := by
    rw [show titsT i = CFSG.Sporadic.Schreier.Tits.titsT i from congrFun Tits_titsT_eq i, Tits_titsDerivedArrs_eq]
    exact CFSG.Sporadic.Schreier.Tits.titsT_rep hi
  titsDerivedArrs_get {j} hj := by
    rw [Tits_titsDerivedArrs_eq, Tits_unpack_eq, TitsText_F_eq]
    exact CertificateChecks.KernelMisc.TitsText.titsDerivedArrs_get hj

end CFSGOutsideClean.Corpus
