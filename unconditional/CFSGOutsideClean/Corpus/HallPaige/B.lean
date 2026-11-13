import CFSG.Monster.Existence.MilestoneInputs
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElems
import CFSG.Monster.Existence.BabyW2Classes
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
import CFSG.Sporadic.Bridge.BBound
import Certificates.Certificate17101
import Certificates.Certificate17450
import CFSG.Monster.B.Pinned.GeneratorDeterminants
import CFSG.Certificates.Kernel.BabyMonster.Sound
import Certificates.Kernel.BabyMonster.FiveA.RankLin
import CFSGOutside.Corpus.HallPaige.B
import CFSGOutsideClean.Corpus.HallPaige.Defs.B

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.B` assumes. -/

open CFSGOutsideClean.Corpus in
instance CFSGOutsideClean.Corpus.hpBTheorems : CFSGOutside.Corpus.B.Theorems :=
  ⟨CFSG.Monster.Existence.babyTableIII,
    CFSG.Monster.Existence.babyTableIV,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.babyInv_zero_of_rank_1860,
    CFSG.Monster.Existence.babyInv_one_of_rank_2048,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.babyInv_three_of_rank_2158,
    CFSG.Sporadic.Bridge.B.nonempty_mulEquiv,
    Certificates.certificate17101,
    Certificates.certificate17450,
    CFSG.Monster.B.genA₁_mul_self,
    fun hW hA h => CFSG.KC.BM.stripMat_mul_of_allStrips hW hA (B_allStrips_iff.mp h),
    fun hW hA h => CFSG.KC.BM.stripMat_mul_eq_one hW hA (B_allStrips_iff.mp h),
    fun hk hM hP hR hrk hs he =>
      CertificateChecks.KernelBM.FiveA.rank_sub_one_of_cert hk hM hP hR (B_allStripsX_iff.mp hrk) hs he⟩
