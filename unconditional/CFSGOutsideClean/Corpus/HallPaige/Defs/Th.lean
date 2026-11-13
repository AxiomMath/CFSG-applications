import CFSG.Sporadic.Th.Setup
import CFSG.Certificates.Kernel.ThDemp.OrbBound
import CFSG.Certificates.Kernel.ThDemp.ChainExBase
import Certificates.Kernel.ThDemp.OrbData
import CFSGOutside.Corpus.HallPaige.Th
import CFSGOutsideClean.Corpus.HallPaige.Defs.ThKernel

/-!
The definitions copied into `CFSGOutside.Corpus.HallPaige.Th` are the corpus definitions.

The copied structures `DempData`, `OrbData`, `DempFacts`, `Bound.OrbChecks`, `Stab.Ctx` and
`OrbMain.SuborbitHyp` are new inductive types, so they are transported field by field to the corpus
structures. Each field agrees with its corpus counterpart through the per-definition lemmas of
`Defs/ThKernel.lean`. The copied data agree with the corpus data literal for literal.
-/

set_option maxRecDepth 400000

namespace CFSGOutsideClean.Corpus.Th

open MulAction

theorem matA_eq : CFSGOutside.Corpus.Th.Sporadic.Th.matA = CFSG.Sporadic.Th.matA := by
  with_unfolding_all rfl

theorem matB_eq : CFSGOutside.Corpus.Th.Sporadic.Th.matB = CFSG.Sporadic.Th.matB := by
  with_unfolding_all rfl

theorem nativeTh_eq :
    CFSGOutside.Corpus.Th.Blueprint.NativeSporadic.Th = CFSG.Blueprint.NativeSporadic.Th := by
  with_unfolding_all rfl

theorem pkMat_eq : @CFSGOutside.Corpus.Th.KC.Th.Spec.pkMat = @CFSG.KC.Th.Spec.pkMat :=
  K.KC_Th_Spec_pkMat

theorem mulB_eq : @CFSGOutside.Corpus.Th.KC.Th.mulB = @CFSG.KC.Th.mulB :=
  K.KC_Th_mulB

theorem constsOK_eq : @CFSGOutside.Corpus.Th.KC.Th.BigS.constsOK = @CFSG.KC.Th.BigS.constsOK :=
  K.KC_Th_BigS_constsOK

theorem rep_eq : @CFSGOutside.Corpus.Th.KC.Th.BigS.rep = @CFSG.KC.Th.BigS.rep :=
  K.KC_Th_BigS_rep

theorem combChk_eq : @CFSGOutside.Corpus.Th.KC.ThDemp.combChk = @CFSG.KC.ThDemp.combChk :=
  K.KC_ThDemp_combChk

theorem sp_eq : @CFSGOutside.Corpus.Th.Certificates.ThDemp.Act.sp = @CFSG.Certificates.ThDemp.Act.sp := by
  with_unfolding_all rfl

theorem mapM_eq :
    @CFSGOutside.Corpus.Th.Certificates.ThDemp.Act.mapM = @CFSG.Certificates.ThDemp.Act.mapM := by
  with_unfolding_all rfl

theorem dempTo_dempData :
    dempTo CFSGOutside.Corpus.Th.KernelThDemp.dempData = CertificateChecks.KernelThDemp.dempData := by
  with_unfolding_all rfl

theorem orbTo_orbData :
    orbTo CFSGOutside.Corpus.Th.KernelThDemp.orbData = CertificateChecks.KernelThDemp.orbData := by
  with_unfolding_all rfl

variable {D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData} {O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData}

theorem dempChk_eq :
    CFSGOutside.Corpus.Th.KC.ThDemp.dempChk D = CFSG.KC.ThDemp.dempChk (dempTo D) :=
  K.KC_ThDemp_dempChk D

theorem invChk_eq :
    CFSGOutside.Corpus.Th.KC.ThDemp.invChk D O = CFSG.KC.ThDemp.invChk (dempTo D) (orbTo O) :=
  K.KC_ThDemp_invChk D O

theorem dempFacts_of (h : CFSG.Certificates.ThDemp.DempFacts (dempTo D)) :
    CFSGOutside.Corpus.Th.Certificates.ThDemp.DempFacts D where
  consts := h.consts
  rb1 := h.rb1
  rb2 := h.rb2
  slp1 := h.slp1
  slp2 := h.slp2
  nreg_lt := h.nreg_lt
  rd := h.rd
  pr := h.pr
  npr2 := h.npr2
  pr0 := h.pr0
  pr1 := h.pr1
  marks_ok := h.marks_ok
  L6 := h.L6
  osz := h.osz
  fr0 := h.fr0
  frL := h.frL
  mono := h.mono
  bv_lt := h.bv_lt
  P0 := h.P0
  tr0 := h.tr0
  tree := h.tree
  inj := h.inj
  fix := h.fix
  res := h.res

theorem dempFacts_to (h : CFSGOutside.Corpus.Th.Certificates.ThDemp.DempFacts D) :
    CFSG.Certificates.ThDemp.DempFacts (dempTo D) where
  consts := h.consts
  rb1 := h.rb1
  rb2 := h.rb2
  slp1 := h.slp1
  slp2 := h.slp2
  nreg_lt := h.nreg_lt
  rd := h.rd
  pr := h.pr
  npr2 := h.npr2
  pr0 := h.pr0
  pr1 := h.pr1
  marks_ok := h.marks_ok
  L6 := h.L6
  osz := h.osz
  fr0 := h.fr0
  frL := h.frL
  mono := h.mono
  bv_lt := h.bv_lt
  P0 := h.P0
  tr0 := h.tr0
  tree := h.tree
  inj := h.inj
  fix := h.fix
  res := h.res

theorem lget_eq : @CFSGOutside.Corpus.Th.KC.ThDemp.lget = @CFSG.KC.ThDemp.lget :=
  K.KC_ThDemp_lget

theorem lgetL_eq : @CFSGOutside.Corpus.Th.KC.ThDemp.lgetL = @CFSG.KC.ThDemp.lgetL :=
  K.KC_ThDemp_lgetL

theorem sOf_eq :
    @CFSGOutside.Corpus.Th.Certificates.ThDemp.OrbMain.sOf =
      @CFSG.Certificates.ThDemp.OrbMain.sOf := by
  with_unfolding_all rfl

theorem orbChecks_of (h : CFSG.Certificates.ThDemp.Bound.OrbChecks (dempTo D) (orbTo O)) :
    CFSGOutside.Corpus.Th.Certificates.ThDemp.Bound.OrbChecks D O where
  inv := by rw [invChk_eq]; exact h.inv
  batch i hi y3 hy3 := by rw [K.KC_ThDemp_batchChk]; exact h.batch i hi y3 hy3
  cross56 y3 hy3 := by rw [K.KC_ThDemp_crossChk]; exact h.cross56 y3 hy3
  cross78 y3 hy3 := by rw [K.KC_ThDemp_crossChk]; exact h.cross78 y3 hy3
  ky i hi := by rw [K.KC_ThDemp_kyChk]; exact h.ky i hi
  low i hi := by rw [K.KC_ThDemp_lowChk]; exact h.low i hi
  orb := by rw [K.KC_ThDemp_orbChk]; exact h.orb
  codes := by rw [K.KC_ThDemp_codesChk]; exact h.codes
  elt1 := by rw [K.KC_ThDemp_eltChk1]; exact h.elt1
  cent := by rw [K.KC_ThDemp_centChk]; exact h.cent
  q := by rw [K.KC_ThDemp_qChk]; exact h.q
  norm := by rw [K.KC_ThDemp_normChk]; exact h.norm
  sb i := by rw [lget_eq, sOf_eq]; exact h.sb i
  w9 := by rw [lgetL_eq]; exact h.w9

theorem orbChecks_to (h : CFSGOutside.Corpus.Th.Certificates.ThDemp.Bound.OrbChecks D O) :
    CFSG.Certificates.ThDemp.Bound.OrbChecks (dempTo D) (orbTo O) where
  inv := by rw [← invChk_eq]; exact h.inv
  batch i hi y3 hy3 := by rw [← K.KC_ThDemp_batchChk]; exact h.batch i hi y3 hy3
  cross56 y3 hy3 := by rw [← K.KC_ThDemp_crossChk]; exact h.cross56 y3 hy3
  cross78 y3 hy3 := by rw [← K.KC_ThDemp_crossChk]; exact h.cross78 y3 hy3
  ky i hi := by rw [← K.KC_ThDemp_kyChk]; exact h.ky i hi
  low i hi := by rw [← K.KC_ThDemp_lowChk]; exact h.low i hi
  orb := by rw [← K.KC_ThDemp_orbChk]; exact h.orb
  codes := by rw [← K.KC_ThDemp_codesChk]; exact h.codes
  elt1 := by rw [← K.KC_ThDemp_eltChk1]; exact h.elt1
  cent := by rw [← K.KC_ThDemp_centChk]; exact h.cent
  q := by rw [← K.KC_ThDemp_qChk]; exact h.q
  norm := by rw [← K.KC_ThDemp_normChk]; exact h.norm
  sb i := by rw [← lget_eq, ← sOf_eq]; exact h.sb i
  w9 := by rw [← lgetL_eq]; exact h.w9

/-- The corpus context with the fields of a copied one. -/
def ctxTo {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (C : CFSGOutside.Corpus.Th.Certificates.ThDemp.Stab.Ctx D O J) :
    CFSG.Certificates.ThDemp.Stab.Ctx (dempTo D) (orbTo O) J where
  d₀ := C.d₀
  d₁ := C.d₁
  t := C.t
  mem := C.mem
  mat := C.mat
  uniq := C.uniq
  inv := C.inv
  osz := C.osz
  md₀ := C.md₀
  md₁ := C.md₁
  lev5 := C.lev5

universe u v

theorem suborbitHyp_to {G : Type u} {X : Type v} [Group G] [MulAction G X] [Finite G]
    {H : Subgroup G} {x : X} {p : Fin 10 → X}
    (h : CFSGOutside.Corpus.Th.Certificates.ThDemp.OrbMain.SuborbitHyp H x p) :
    CFSG.Certificates.ThDemp.OrbMain.SuborbitHyp H x p where
  cardG := h.cardG
  cardD := h.cardD
  fixD := h.fixD
  mem := h.mem
  stab := h.stab
  orb9 := h.orb9
  dis56 := h.dis56
  dis78 := h.dis78

theorem pts_eq {X : Type v} :
    @CFSGOutside.Corpus.Th.Certificates.ThDemp.OrbMain.pts X =
      @CFSG.Certificates.ThDemp.OrbMain.pts X := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus.Th
