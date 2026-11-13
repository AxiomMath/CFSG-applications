import CFSG.Sporadic.Th.Setup
import CFSG.Sporadic.Bridge.ThSurj
import CFSG.Certificates.Kernel.ThDemp.Sound
import CFSG.Certificates.Kernel.ThDemp.ChainEx
import CFSG.Certificates.Kernel.ThDemp.OrbUnfold
import CFSG.Certificates.Kernel.ThDemp.OrbBound
import CFSG.Certificates.Kernel.ThDemp.Action
import CFSG.Certificates.Kernel.ThDemp.OrbMain
import CFSG.Certificates.Kernel.Th.Spec.Big
import Certificates.Kernel.ThDemp.AssemblyBase
import Certificates.Kernel.ThDemp.OrbAssemblyBase
import CFSGOutsideClean.Corpus.HallPaige.Defs.Th

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Th` assumes. -/

set_option maxRecDepth 400000

namespace CFSGOutsideClean.Corpus

open CFSGOutsideClean.Corpus.Th

instance hpThSeed : CFSGOutside.Corpus.Th.Sporadic.Th.Seed where
  matA_mul_self := by
    rw [matA_eq]
    exact CFSG.Sporadic.Th.matA_mul_self
  matB_cube := by
    rw [matB_eq]
    exact CFSG.Sporadic.Th.matB_cube

instance hpThTheorems : CFSGOutside.Corpus.Th.Theorems where
  seed := hpThSeed
  nonempty_mulEquiv := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  card_J := CFSG.Sporadic.Bridge.Th.card_J
  dempChk_facts D h := by
    rw [dempChk_eq] at h
    exact dempFacts_of (CFSG.Certificates.ThDemp.dempChk_facts (dempTo D) h)
  demp_chk := by
    rw [dempChk_eq, dempTo_dempData]
    exact CertificateChecks.KernelThDemp.demp_chk
  pkMat_SA := by
    rw [pkMat_eq, matA_eq]
    exact CertificateChecks.KernelThDemp.pkMat_SA
  pkMat_SB := by
    rw [pkMat_eq, matB_eq]
    exact CertificateChecks.KernelThDemp.pkMat_SB
  pkMat_mulB h A B := by
    rw [constsOK_eq] at h
    rw [pkMat_eq, mulB_eq]
    exact CFSG.KC.Th.Spec.pkMat_mulB h A B
  pkMat_one h := by
    rw [constsOK_eq] at h
    rw [pkMat_eq]
    exact CFSG.KC.Th.Spec.pkMat_one h
  exists_chain := by
    intro D hF J a b ha hb
    exact CFSG.Certificates.ThDemp.exists_chain (dempFacts_to hF) ha hb
  invChk_sound h := by
    rw [invChk_eq] at h
    exact CFSG.Certificates.ThDemp.Unfold.invChk_sound h
  orb_checks := by
    have h := CertificateChecks.KernelThDemp.orb_checks
    rw [← dempTo_dempData, ← orbTo_orbData] at h
    exact orbChecks_of h
  suborbitHyp C hF hJ hc _ hcard hD := by
    have h := CFSG.Certificates.ThDemp.Bound.Ctx.suborbitHyp (ctxTo C) (dempFacts_to hF) hJ
      (orbChecks_to hc) hcard hD
    exact ⟨h.cardG, h.cardD, h.fixD, h.mem, h.stab, h.orb9, h.dis56, h.dis78⟩
  sp_mulB P N := by
    rw [sp_eq, mulB_eq, rep_eq, mapM_eq, pkMat_eq]
    exact CFSG.Certificates.ThDemp.Act.sp_mulB P N
  sp_le_of_combChk h := by
    rw [combChk_eq] at h
    rw [sp_eq]
    exact CFSG.Certificates.ThDemp.Act.sp_le_of_combChk h

universe u v

instance hpThGeneric : CFSGOutside.Corpus.Th.Generic.{u, v} where
  cover H := CFSG.Certificates.ThDemp.OrbMain.SuborbitHyp.cover (suborbitHyp_to H)

end CFSGOutsideClean.Corpus
