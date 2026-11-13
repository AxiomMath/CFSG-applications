import CFSG.Sporadic.Presentation.Ly
import Certificates.Certificate3085
import Certificates.Kernel.Ly3085.Bridge
import Certificates.Kernel.Ly3085.Squeeze
import CFSGOutside.Corpus.HallPaige.Ly
import CFSGOutsideClean.Corpus.HallPaige.Defs.Ly

/-! The corpus proves the statements that `CFSGOutside.Corpus.HallPaige.Ly` assumes. -/

instance CFSGOutsideClean.Corpus.hpLyTheorems : CFSGOutside.Corpus.Ly.Theorems where
  lySeed := CFSGOutsideClean.Corpus.Ly.lySeed
  F1_all := CFSGOutsideClean.Corpus.Ly.F1_all
  one_facts := by
    rw [CFSGOutsideClean.Corpus.Ly.BC_ONEF_eq]
    exact CertificateChecks.KernelLy.Omega.one_facts
  fmul hX hY := by
    rw [CFSGOutsideClean.Corpus.Ly.fMul_eq]
    exact CertificateChecks.KernelLy.Omega.fmul hX hY
  aStar_zero := CertificateChecks.KernelLy.Omega.aStar_zero
  aStar_one := CertificateChecks.KernelLy.Omega.aStar_one
  af_facts hj := by
    rw [CFSGOutsideClean.Corpus.Ly.AF_eq, CFSGOutsideClean.Corpus.Ly.AI_eq]
    exact CertificateChecks.KernelLy.Omega.af_facts hj
  bridge_hom := Certificates.certificate3085.bridge_hom
  finite_card_le := CFSG.Sporadic.Presentation.Ly.finite_card_le
