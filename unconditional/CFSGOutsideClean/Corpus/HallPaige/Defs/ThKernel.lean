import CFSG.Certificates.Kernel.ThDemp.OrbBound
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSGOutside.Corpus.HallPaige.Th.Kernel

/-!
The definitions copied into `CFSGOutside.Corpus.HallPaige.Th.Kernel` are the corpus definitions.

Generated from the copy, one lemma per definition in its order. For each copied
definition, unfolding it and its corpus original once and rewriting the copied definitions it uses by
their own agreement lemmas leaves the same term on both sides. The copied structures `DempData` and
`OrbData` are new types, so a definition taking them is compared with its corpus original at the corpus
structure with the same fields (`dempTo`, `orbTo`). Unfolding everything at once instead makes the
unifier and the kernel unroll the literal-bounded recursors of the checkers, which does not finish.
-/

namespace CFSGOutsideClean.Corpus.Th

/-- The corpus `DempData` with the fields of a copied one. -/
abbrev dempTo (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) : CFSG.KC.ThDemp.DempData where
  c := D.c
  rm := D.rm
  tm0 := D.tm0
  tm1 := D.tm1
  tm2 := D.tm2
  tm3 := D.tm3
  tm4 := D.tm4
  tm5 := D.tm5
  tm6 := D.tm6
  tm7 := D.tm7
  up := D.up
  dg := D.dg
  ONE := D.ONE
  SA := D.SA
  SB := D.SB
  regs := D.regs
  cs1 := D.cs1
  cs2 := D.cs2
  r1 := D.r1
  nreg := D.nreg
  rd := D.rd
  pr := D.pr
  npr := D.npr
  L := D.L
  fr := D.fr
  bv := D.bv
  osz := D.osz
  pts := D.pts
  tr := D.tr
  tree := D.tree
  ord := D.ord
  res := D.res

/-- The corpus `OrbData` with the fields of a copied one. -/
abbrev orbTo (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData) : CFSG.KC.ThDemp.OrbData where
  Ti := O.Ti
  words := O.words
  sb := O.sb
  grp := O.grp
  ky := O.ky
  par := O.par
  edges := O.edges
  ord := O.ord
  fx5 := O.fx5
  x5 := O.x5
  x31 := O.x31
  yb := O.yb
  dm := O.dm
  f5 := O.f5
  v5 := O.v5
  qm := O.qm
  gs5 := O.gs5
  gs31 := O.gs31
  Ga := O.Ga
  Gb := O.Gb
  gd0 := O.gd0
  gd1 := O.gd1

namespace K

theorem KC_Loop_strictN :
    @CFSGOutside.Corpus.Th.KC.Loop.strictN =
      @CFSG.KC.Loop.strictN := by
  delta CFSGOutside.Corpus.Th.KC.Loop.strictN CFSG.KC.Loop.strictN
  rfl

theorem KC_Loop_allBelow :
    @CFSGOutside.Corpus.Th.KC.Loop.allBelow =
      @CFSG.KC.Loop.allBelow := by
  delta CFSGOutside.Corpus.Th.KC.Loop.allBelow CFSG.KC.Loop.allBelow
  rfl

theorem KC_Loop_sumBelow :
    @CFSGOutside.Corpus.Th.KC.Loop.sumBelow =
      @CFSG.KC.Loop.sumBelow := by
  delta CFSGOutside.Corpus.Th.KC.Loop.sumBelow CFSG.KC.Loop.sumBelow
  rfl

theorem KC_Th_andB :
    @CFSGOutside.Corpus.Th.KC.Th.andB =
      @CFSG.KC.Th.andB := by
  delta CFSGOutside.Corpus.Th.KC.Th.andB CFSG.KC.Th.andB
  rfl

theorem KC_Th_mstep :
    @CFSGOutside.Corpus.Th.KC.Th.mstep =
      @CFSG.KC.Th.mstep := by
  delta CFSGOutside.Corpus.Th.KC.Th.mstep CFSG.KC.Th.mstep
  rfl

theorem KC_Th_mulB :
    @CFSGOutside.Corpus.Th.KC.Th.mulB =
      @CFSG.KC.Th.mulB := by
  delta CFSGOutside.Corpus.Th.KC.Th.mulB CFSG.KC.Th.mulB
  try rw [KC_Th_mstep]
  all_goals rfl

theorem KC_Th_vecB :
    @CFSGOutside.Corpus.Th.KC.Th.vecB =
      @CFSG.KC.Th.vecB := by
  delta CFSGOutside.Corpus.Th.KC.Th.vecB CFSG.KC.Th.vecB
  rfl

theorem KC_Th_BigS_bitsN :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.bitsN =
      @CFSG.KC.Th.BigS.bitsN := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.bitsN CFSG.KC.Th.BigS.bitsN
  rfl

theorem KC_Th_BigS_notB :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.notB =
      @CFSG.KC.Th.BigS.notB := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.notB CFSG.KC.Th.BigS.notB
  rfl

theorem KC_Th_BigS_rep :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.rep =
      @CFSG.KC.Th.BigS.rep := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.rep CFSG.KC.Th.BigS.rep
  rfl

theorem KC_Th_BigS_tmask :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.tmask =
      @CFSG.KC.Th.BigS.tmask := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.tmask CFSG.KC.Th.BigS.tmask
  rfl

theorem KC_Th_BigS_upper :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.upper =
      @CFSG.KC.Th.BigS.upper := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.upper CFSG.KC.Th.BigS.upper
  rfl

theorem KC_Th_BigS_constsOK :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.constsOK =
      @CFSG.KC.Th.BigS.constsOK := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.constsOK CFSG.KC.Th.BigS.constsOK
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_rep]
  try rw [KC_Th_BigS_tmask]
  try rw [KC_Th_BigS_upper]
  all_goals rfl

theorem KC_Th_BigS_powB :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.powB =
      @CFSG.KC.Th.BigS.powB := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.powB CFSG.KC.Th.BigS.powB
  try rw [KC_Th_mulB]
  all_goals rfl

theorem KC_Th_BigS_regBelow :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.regBelow =
      @CFSG.KC.Th.BigS.regBelow := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.regBelow CFSG.KC.Th.BigS.regBelow
  try rw [KC_Th_andB]
  all_goals rfl

theorem KC_Th_BigS_insOK :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.insOK =
      @CFSG.KC.Th.BigS.insOK := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.insOK CFSG.KC.Th.BigS.insOK
  try rw [KC_Th_andB]
  try rw [KC_Th_mulB]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_Th_BigS_powB]
  try rw [KC_Th_BigS_regBelow]
  all_goals rfl

theorem KC_Th_BigS_runSlp :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.runSlp =
      @CFSG.KC.Th.BigS.runSlp := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.runSlp CFSG.KC.Th.BigS.runSlp
  try rw [KC_Loop_strictN]
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_Th_BigS_insOK]
  all_goals rfl

theorem KC_Th_BigS_marked :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.marked =
      @CFSG.KC.Th.BigS.marked := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.marked CFSG.KC.Th.BigS.marked
  rfl

theorem KC_Th_BigS_runMarked :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.runMarked =
      @CFSG.KC.Th.BigS.runMarked := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.runMarked CFSG.KC.Th.BigS.runMarked
  try rw [KC_Loop_strictN]
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_Th_BigS_marked]
  all_goals rfl

theorem KC_Th_BigS_regAt :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.regAt =
      @CFSG.KC.Th.BigS.regAt := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.regAt CFSG.KC.Th.BigS.regAt
  try rw [KC_Th_BigS_bitsN]
  all_goals rfl

theorem KC_Th_BigS_regsIn :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.regsIn =
      @CFSG.KC.Th.BigS.regsIn := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.regsIn CFSG.KC.Th.BigS.regsIn
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_regBelow]
  try rw [KC_Th_BigS_regAt]
  all_goals rfl

theorem KC_Th_BigS_allMarked :
    @CFSGOutside.Corpus.Th.KC.Th.BigS.allMarked =
      @CFSG.KC.Th.BigS.allMarked := by
  delta CFSGOutside.Corpus.Th.KC.Th.BigS.allMarked CFSG.KC.Th.BigS.allMarked
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_marked]
  try rw [KC_Th_BigS_regAt]
  all_goals rfl

theorem KC_Th_Spec_pkMat :
    @CFSGOutside.Corpus.Th.KC.Th.Spec.pkMat =
      @CFSG.KC.Th.Spec.pkMat := by
  delta CFSGOutside.Corpus.Th.KC.Th.Spec.pkMat CFSG.KC.Th.Spec.pkMat
  rfl

theorem KC_Th_Spec_pkVec :
    @CFSGOutside.Corpus.Th.KC.Th.Spec.pkVec =
      @CFSG.KC.Th.Spec.pkVec := by
  delta CFSGOutside.Corpus.Th.KC.Th.Spec.pkVec CFSG.KC.Th.Spec.pkVec
  rfl

theorem KC_ThDemp_lget :
    @CFSGOutside.Corpus.Th.KC.ThDemp.lget =
      @CFSG.KC.ThDemp.lget := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.lget CFSG.KC.ThDemp.lget
  rfl

theorem KC_ThDemp_lgetL :
    @CFSGOutside.Corpus.Th.KC.ThDemp.lgetL =
      @CFSG.KC.ThDemp.lgetL := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.lgetL CFSG.KC.ThDemp.lgetL
  rfl

theorem KC_ThDemp_DempData_RB : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.RB D =
      @CFSG.KC.ThDemp.DempData.RB (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.RB CFSG.KC.ThDemp.DempData.RB
  try rw [KC_ThDemp_lget]
  all_goals rfl

theorem KC_ThDemp_DempData_S : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.S D =
      @CFSG.KC.ThDemp.DempData.S (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.S CFSG.KC.ThDemp.DempData.S
  try rw [KC_Th_BigS_regAt]
  try rw [KC_ThDemp_DempData_RB]
  all_goals rfl

theorem KC_ThDemp_DempData_trR : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.trR D =
      @CFSG.KC.ThDemp.DempData.trR (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.trR CFSG.KC.ThDemp.DempData.trR
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_lgetL]
  all_goals rfl

theorem KC_ThDemp_DempData_T : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.T D =
      @CFSG.KC.ThDemp.DempData.T (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.T CFSG.KC.ThDemp.DempData.T
  try rw [KC_ThDemp_DempData_RB]
  try rw [KC_ThDemp_DempData_trR]
  all_goals rfl

theorem KC_ThDemp_DempData_P : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.P D =
      @CFSG.KC.ThDemp.DempData.P (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.P CFSG.KC.ThDemp.DempData.P
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_lgetL]
  all_goals rfl

theorem KC_ThDemp_DempData_frL : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.frL D =
      @CFSG.KC.ThDemp.DempData.frL (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.frL CFSG.KC.ThDemp.DempData.frL
  try rw [KC_ThDemp_lget]
  all_goals rfl

theorem KC_ThDemp_DempData_oszL : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.oszL D =
      @CFSG.KC.ThDemp.DempData.oszL (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.oszL CFSG.KC.ThDemp.DempData.oszL
  try rw [KC_ThDemp_lget]
  all_goals rfl

theorem KC_ThDemp_DempData_bvL : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.bvL D =
      @CFSG.KC.ThDemp.DempData.bvL (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.bvL CFSG.KC.ThDemp.DempData.bvL
  try rw [KC_ThDemp_lget]
  all_goals rfl

theorem KC_ThDemp_DempData_mul : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.mul D =
      @CFSG.KC.ThDemp.DempData.mul (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.mul CFSG.KC.ThDemp.DempData.mul
  try rw [KC_Th_mulB]
  all_goals rfl

theorem KC_ThDemp_DempData_stepY : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.stepY D =
      @CFSG.KC.ThDemp.DempData.stepY (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.stepY CFSG.KC.ThDemp.DempData.stepY
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_mul]
  all_goals rfl

theorem KC_ThDemp_DempData_sift : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.sift D =
      @CFSG.KC.ThDemp.DempData.sift (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.sift CFSG.KC.ThDemp.DempData.sift
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_DempData_stepY]
  all_goals rfl

theorem KC_ThDemp_slpChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.slpChk D =
      @CFSG.KC.ThDemp.slpChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.slpChk CFSG.KC.ThDemp.slpChk
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_constsOK]
  try rw [KC_Th_BigS_runSlp]
  try rw [KC_ThDemp_DempData_RB]
  all_goals rfl

theorem KC_ThDemp_DempData_marks : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.DempData.marks D =
      @CFSG.KC.ThDemp.DempData.marks (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.DempData.marks CFSG.KC.ThDemp.DempData.marks
  try rw [KC_Th_BigS_regAt]
  all_goals rfl

theorem KC_ThDemp_markChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.markChk D =
      @CFSG.KC.ThDemp.markChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.markChk CFSG.KC.ThDemp.markChk
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_runMarked]
  try rw [KC_Th_BigS_regAt]
  try rw [KC_Th_BigS_regsIn]
  try rw [KC_Th_BigS_allMarked]
  try rw [KC_ThDemp_DempData_marks]
  all_goals rfl

theorem KC_ThDemp_frChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.frChk D =
      @CFSG.KC.ThDemp.frChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.frChk CFSG.KC.ThDemp.frChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_DempData_frL]
  all_goals rfl

theorem KC_ThDemp_levelChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.levelChk D =
      @CFSG.KC.ThDemp.levelChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.levelChk CFSG.KC.ThDemp.levelChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_Th_vecB]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_lgetL]
  try rw [KC_ThDemp_DempData_RB]
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_DempData_trR]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_DempData_frL]
  try rw [KC_ThDemp_DempData_oszL]
  try rw [KC_ThDemp_DempData_bvL]
  try rw [KC_ThDemp_DempData_mul]
  all_goals rfl

theorem KC_ThDemp_resChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.resChk D =
      @CFSG.KC.ThDemp.resChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.resChk CFSG.KC.ThDemp.resChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_lgetL]
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_frL]
  try rw [KC_ThDemp_DempData_oszL]
  try rw [KC_ThDemp_DempData_mul]
  try rw [KC_ThDemp_DempData_sift]
  all_goals rfl

theorem KC_ThDemp_shapeChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.shapeChk D =
      @CFSG.KC.ThDemp.shapeChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.shapeChk CFSG.KC.ThDemp.shapeChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_DempData_oszL]
  try rw [KC_ThDemp_markChk]
  try rw [KC_ThDemp_frChk]
  all_goals rfl

theorem KC_ThDemp_levelsChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.levelsChk D =
      @CFSG.KC.ThDemp.levelsChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.levelsChk CFSG.KC.ThDemp.levelsChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_levelChk]
  all_goals rfl

theorem KC_ThDemp_dempChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.dempChk D =
      @CFSG.KC.ThDemp.dempChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.dempChk CFSG.KC.ThDemp.dempChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_slpChk]
  try rw [KC_ThDemp_resChk]
  try rw [KC_ThDemp_shapeChk]
  try rw [KC_ThDemp_levelsChk]
  all_goals rfl

theorem KC_ThDemp_strictB :
    @CFSGOutside.Corpus.Th.KC.ThDemp.strictB =
      @CFSG.KC.ThDemp.strictB := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.strictB CFSG.KC.ThDemp.strictB
  rfl

theorem KC_ThDemp_strictL :
    @CFSGOutside.Corpus.Th.KC.ThDemp.strictL =
      @CFSG.KC.ThDemp.strictL := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.strictL CFSG.KC.ThDemp.strictL
  rfl

theorem KC_ThDemp_m1280 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.m1280 =
      @CFSG.KC.ThDemp.m1280 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.m1280 CFSG.KC.ThDemp.m1280
  rfl

theorem KC_ThDemp_ptAt :
    @CFSGOutside.Corpus.Th.KC.ThDemp.ptAt =
      @CFSG.KC.ThDemp.ptAt := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.ptAt CFSG.KC.ThDemp.ptAt
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_m1280]
  all_goals rfl

theorem KC_ThDemp_repD :
    @CFSGOutside.Corpus.Th.KC.ThDemp.repD =
      @CFSG.KC.ThDemp.repD := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.repD CFSG.KC.ThDemp.repD
  rfl

theorem KC_ThDemp_repN :
    @CFSGOutside.Corpus.Th.KC.ThDemp.repN =
      @CFSG.KC.ThDemp.repN := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.repN CFSG.KC.ThDemp.repN
  try rw [KC_ThDemp_repD]
  all_goals rfl

theorem KC_ThDemp_m63 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.m63 =
      @CFSG.KC.ThDemp.m63 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.m63 CFSG.KC.ThDemp.m63
  rfl

theorem KC_ThDemp_m64 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.m64 =
      @CFSG.KC.ThDemp.m64 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.m64 CFSG.KC.ThDemp.m64
  rfl

theorem KC_ThDemp_and5 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.and5 =
      @CFSG.KC.ThDemp.and5 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.and5 CFSG.KC.ThDemp.and5
  rfl

theorem KC_ThDemp_subX :
    @CFSGOutside.Corpus.Th.KC.ThDemp.subX =
      @CFSG.KC.ThDemp.subX := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.subX CFSG.KC.ThDemp.subX
  try rw [KC_ThDemp_and5]
  all_goals rfl

theorem KC_ThDemp_fold64 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.fold64 =
      @CFSG.KC.ThDemp.fold64 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.fold64 CFSG.KC.ThDemp.fold64
  rfl

theorem KC_ThDemp_rowsOf :
    @CFSGOutside.Corpus.Th.KC.ThDemp.rowsOf =
      @CFSG.KC.ThDemp.rowsOf := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.rowsOf CFSG.KC.ThDemp.rowsOf
  try rw [KC_ThDemp_DempData_P]
  all_goals rfl

theorem KC_ThDemp_keyL :
    @CFSGOutside.Corpus.Th.KC.ThDemp.keyL =
      @CFSG.KC.ThDemp.keyL := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.keyL CFSG.KC.ThDemp.keyL
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_m63]
  try rw [KC_ThDemp_subX]
  try rw [KC_ThDemp_fold64]
  try rw [KC_ThDemp_rowsOf]
  all_goals rfl

theorem KC_ThDemp_combsL :
    @CFSGOutside.Corpus.Th.KC.ThDemp.combsL =
      @CFSG.KC.ThDemp.combsL := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.combsL CFSG.KC.ThDemp.combsL
  rfl

theorem KC_ThDemp_notMemB :
    @CFSGOutside.Corpus.Th.KC.ThDemp.notMemB =
      @CFSG.KC.ThDemp.notMemB := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.notMemB CFSG.KC.ThDemp.notMemB
  try rw [KC_Th_andB]
  all_goals rfl

theorem KC_ThDemp_nodupB :
    @CFSGOutside.Corpus.Th.KC.ThDemp.nodupB =
      @CFSG.KC.ThDemp.nodupB := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.nodupB CFSG.KC.ThDemp.nodupB
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_notMemB]
  all_goals rfl

theorem KC_ThDemp_keyB :
    @CFSGOutside.Corpus.Th.KC.ThDemp.keyB =
      @CFSG.KC.ThDemp.keyB := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.keyB CFSG.KC.ThDemp.keyB
  try rw [KC_Loop_strictN]
  try rw [KC_ThDemp_subX]
  try rw [KC_ThDemp_fold64]
  all_goals rfl

theorem KC_ThDemp_packD :
    @CFSGOutside.Corpus.Th.KC.ThDemp.packD =
      @CFSG.KC.ThDemp.packD := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.packD CFSG.KC.ThDemp.packD
  try rw [KC_ThDemp_m64]
  all_goals rfl

theorem KC_ThDemp_stackN :
    @CFSGOutside.Corpus.Th.KC.ThDemp.stackN =
      @CFSG.KC.ThDemp.stackN := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.stackN CFSG.KC.ThDemp.stackN
  rfl

theorem KC_ThDemp_keyAt :
    @CFSGOutside.Corpus.Th.KC.ThDemp.keyAt =
      @CFSG.KC.ThDemp.keyAt := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.keyAt CFSG.KC.ThDemp.keyAt
  try rw [KC_ThDemp_m64]
  all_goals rfl

theorem KC_ThDemp_bitB :
    @CFSGOutside.Corpus.Th.KC.ThDemp.bitB =
      @CFSG.KC.ThDemp.bitB := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.bitB CFSG.KC.ThDemp.bitB
  rfl

theorem KC_ThDemp_jz :
    @CFSGOutside.Corpus.Th.KC.ThDemp.jz =
      @CFSG.KC.ThDemp.jz := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.jz CFSG.KC.ThDemp.jz
  rfl

theorem KC_ThDemp_combRow :
    @CFSGOutside.Corpus.Th.KC.ThDemp.combRow =
      @CFSG.KC.ThDemp.combRow := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.combRow CFSG.KC.ThDemp.combRow
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_DempData_P]
  all_goals rfl

theorem KC_ThDemp_combChk :
    @CFSGOutside.Corpus.Th.KC.ThDemp.combChk =
      @CFSG.KC.ThDemp.combChk := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.combChk CFSG.KC.ThDemp.combChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_combRow]
  all_goals rfl

theorem KC_ThDemp_lgetLL :
    @CFSGOutside.Corpus.Th.KC.ThDemp.lgetLL =
      @CFSG.KC.ThDemp.lgetLL := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.lgetLL CFSG.KC.ThDemp.lgetLL
  rfl

theorem KC_ThDemp_lgetL3 :
    @CFSGOutside.Corpus.Th.KC.ThDemp.lgetL3 =
      @CFSG.KC.ThDemp.lgetL3 := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.lgetL3 CFSG.KC.ThDemp.lgetL3
  rfl

theorem KC_ThDemp_OrbData_TI : ∀ (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.OrbData.TI O =
      @CFSG.KC.ThDemp.OrbData.TI (orbTo O) := by
  intro O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.OrbData.TI CFSG.KC.ThDemp.OrbData.TI
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_lgetL]
  all_goals rfl

theorem KC_ThDemp_OrbData_grpOf : ∀ (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.OrbData.grpOf O =
      @CFSG.KC.ThDemp.OrbData.grpOf (orbTo O) := by
  intro O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.OrbData.grpOf CFSG.KC.ThDemp.OrbData.grpOf
  try rw [KC_ThDemp_lgetLL]
  try rw [KC_ThDemp_lgetL3]
  all_goals rfl

theorem KC_ThDemp_cR :
    @CFSGOutside.Corpus.Th.KC.ThDemp.cR =
      @CFSG.KC.ThDemp.cR := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.cR CFSG.KC.ThDemp.cR
  try rw [KC_Th_BigS_rep]
  all_goals rfl

theorem KC_ThDemp_U0 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.U0 D =
      @CFSG.KC.ThDemp.U0 (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.U0 CFSG.KC.ThDemp.U0
  try rw [KC_ThDemp_DempData_bvL]
  try rw [KC_ThDemp_stackN]
  all_goals rfl

theorem KC_ThDemp_wordR : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.wordR D =
      @CFSG.KC.ThDemp.wordR (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.wordR CFSG.KC.ThDemp.wordR
  try rw [KC_Loop_strictN]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_RB]
  try rw [KC_ThDemp_DempData_S]
  all_goals rfl

theorem KC_ThDemp_pt : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.pt D O =
      @CFSG.KC.ThDemp.pt (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.pt CFSG.KC.ThDemp.pt
  try rw [KC_ThDemp_lgetL]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_U0]
  try rw [KC_ThDemp_wordR]
  all_goals rfl

theorem KC_ThDemp_chainEl : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.chainEl D =
      @CFSG.KC.ThDemp.chainEl (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.chainEl CFSG.KC.ThDemp.chainEl
  try rw [KC_Loop_strictN]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_DempData_mul]
  try rw [KC_ThDemp_DempData_stepY]
  all_goals rfl

theorem KC_ThDemp_invChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.invChk D O =
      @CFSG.KC.ThDemp.invChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.invChk CFSG.KC.ThDemp.invChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_oszL]
  try rw [KC_ThDemp_DempData_mul]
  try rw [KC_ThDemp_OrbData_TI]
  all_goals rfl

theorem KC_ThDemp_xS4 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.xS4 D =
      @CFSG.KC.ThDemp.xS4 (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.xS4 CFSG.KC.ThDemp.xS4
  try rw [KC_Loop_strictN]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_stackN]
  try rw [KC_ThDemp_cR]
  all_goals rfl

theorem KC_ThDemp_xBat : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.xBat D =
      @CFSG.KC.ThDemp.xBat (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.xBat CFSG.KC.ThDemp.xBat
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_strictL]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_xS4]
  all_goals rfl

theorem KC_ThDemp_yBat : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.yBat D O =
      @CFSG.KC.ThDemp.yBat (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.yBat CFSG.KC.ThDemp.yBat
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_strictL]
  try rw [KC_ThDemp_stackN]
  try rw [KC_ThDemp_OrbData_TI]
  try rw [KC_ThDemp_cR]
  all_goals rfl

theorem KC_ThDemp_yKeys : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.yKeys D =
      @CFSG.KC.ThDemp.yKeys (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.yKeys CFSG.KC.ThDemp.yKeys
  try rw [KC_Loop_strictN]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_repN]
  try rw [KC_ThDemp_m63]
  try rw [KC_ThDemp_keyB]
  try rw [KC_ThDemp_packD]
  try rw [KC_ThDemp_stackN]
  all_goals rfl

theorem KC_ThDemp_kyChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.kyChk D O =
      @CFSG.KC.ThDemp.kyChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.kyChk CFSG.KC.ThDemp.kyChk
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_yBat]
  try rw [KC_ThDemp_yKeys]
  all_goals rfl

theorem KC_ThDemp_xKeys : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.xKeys D =
      @CFSG.KC.ThDemp.xKeys (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.xKeys CFSG.KC.ThDemp.xKeys
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_repN]
  try rw [KC_ThDemp_m63]
  try rw [KC_ThDemp_keyB]
  try rw [KC_ThDemp_packD]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_xS4]
  all_goals rfl

theorem KC_ThDemp_maskOf :
    @CFSGOutside.Corpus.Th.KC.ThDemp.maskOf =
      @CFSG.KC.ThDemp.maskOf := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.maskOf CFSG.KC.ThDemp.maskOf
  rfl

theorem KC_ThDemp_flagsOf :
    @CFSGOutside.Corpus.Th.KC.ThDemp.flagsOf =
      @CFSG.KC.ThDemp.flagsOf := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.flagsOf CFSG.KC.ThDemp.flagsOf
  try rw [KC_ThDemp_lget]
  all_goals rfl

theorem KC_ThDemp_batchChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.batchChk D O =
      @CFSG.KC.ThDemp.batchChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.batchChk CFSG.KC.ThDemp.batchChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_repN]
  try rw [KC_ThDemp_keyAt]
  try rw [KC_ThDemp_bitB]
  try rw [KC_ThDemp_jz]
  try rw [KC_ThDemp_OrbData_grpOf]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_xKeys]
  try rw [KC_ThDemp_maskOf]
  try rw [KC_ThDemp_flagsOf]
  all_goals rfl

theorem KC_ThDemp_crossChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.crossChk D O =
      @CFSG.KC.ThDemp.crossChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.crossChk CFSG.KC.ThDemp.crossChk
  try rw [KC_Loop_allBelow]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_repN]
  try rw [KC_ThDemp_keyAt]
  try rw [KC_ThDemp_jz]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_xKeys]
  all_goals rfl

theorem KC_ThDemp_xPt :
    @CFSGOutside.Corpus.Th.KC.ThDemp.xPt =
      @CFSG.KC.ThDemp.xPt := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.xPt CFSG.KC.ThDemp.xPt
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_ptAt]
  all_goals rfl

theorem KC_ThDemp_yPt :
    @CFSGOutside.Corpus.Th.KC.ThDemp.yPt =
      @CFSG.KC.ThDemp.yPt := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.yPt CFSG.KC.ThDemp.yPt
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_ptAt]
  all_goals rfl

theorem KC_ThDemp_pairOK : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.pairOK D =
      @CFSG.KC.ThDemp.pairOK (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.pairOK CFSG.KC.ThDemp.pairOK
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_combChk]
  try rw [KC_ThDemp_xPt]
  try rw [KC_ThDemp_yPt]
  all_goals rfl

theorem KC_ThDemp_groupRun : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.groupRun D =
      @CFSG.KC.ThDemp.groupRun (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.groupRun CFSG.KC.ThDemp.groupRun
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_pairOK]
  all_goals rfl

theorem KC_ThDemp_groupsRun : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.groupsRun D =
      @CFSG.KC.ThDemp.groupsRun (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.groupsRun CFSG.KC.ThDemp.groupsRun
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_groupRun]
  all_goals rfl

theorem KC_ThDemp_batchesRun : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.batchesRun D =
      @CFSG.KC.ThDemp.batchesRun (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.batchesRun CFSG.KC.ThDemp.batchesRun
  try rw [KC_ThDemp_groupsRun]
  all_goals rfl

theorem KC_ThDemp_pairsLen :
    @CFSGOutside.Corpus.Th.KC.ThDemp.pairsLen =
      @CFSG.KC.ThDemp.pairsLen := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.pairsLen CFSG.KC.ThDemp.pairsLen
  rfl

theorem KC_ThDemp_lowChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.lowChk D O =
      @CFSG.KC.ThDemp.lowChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.lowChk CFSG.KC.ThDemp.lowChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_DempData_P]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_lgetL3]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_xBat]
  try rw [KC_ThDemp_yBat]
  try rw [KC_ThDemp_batchesRun]
  try rw [KC_ThDemp_pairsLen]
  all_goals rfl

theorem KC_ThDemp_gen : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.gen D =
      @CFSG.KC.ThDemp.gen (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.gen CFSG.KC.ThDemp.gen
  try rw [KC_Th_BigS_regAt]
  try rw [KC_ThDemp_DempData_RB]
  all_goals rfl

theorem KC_ThDemp_qBuild : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.qBuild D O =
      @CFSG.KC.ThDemp.qBuild (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.qBuild CFSG.KC.ThDemp.qBuild
  try rw [KC_Loop_strictN]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_ptAt]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_gen]
  all_goals rfl

theorem KC_ThDemp_qStack : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.qStack D O =
      @CFSG.KC.ThDemp.qStack (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.qStack CFSG.KC.ThDemp.qStack
  try rw [KC_ThDemp_qBuild]
  all_goals rfl

theorem KC_ThDemp_keys248 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.keys248 D =
      @CFSG.KC.ThDemp.keys248 (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.keys248 CFSG.KC.ThDemp.keys248
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_repN]
  try rw [KC_ThDemp_m63]
  try rw [KC_ThDemp_keyB]
  try rw [KC_ThDemp_packD]
  all_goals rfl

theorem KC_ThDemp_bitsOf :
    @CFSGOutside.Corpus.Th.KC.ThDemp.bitsOf =
      @CFSG.KC.ThDemp.bitsOf := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.bitsOf CFSG.KC.ThDemp.bitsOf
  rfl

theorem KC_ThDemp_orbChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.orbChk D O =
      @CFSG.KC.ThDemp.orbChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.orbChk CFSG.KC.ThDemp.orbChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_andB]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_lget]
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_ptAt]
  try rw [KC_ThDemp_keyAt]
  try rw [KC_ThDemp_bitB]
  try rw [KC_ThDemp_combChk]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_chainEl]
  try rw [KC_ThDemp_gen]
  try rw [KC_ThDemp_qStack]
  try rw [KC_ThDemp_keys248]
  try rw [KC_ThDemp_bitsOf]
  all_goals rfl

theorem KC_ThDemp_uVec : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.uVec D =
      @CFSG.KC.ThDemp.uVec (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.uVec CFSG.KC.ThDemp.uVec
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_DempData_bvL]
  all_goals rfl

theorem KC_ThDemp_uAll : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.uAll D =
      @CFSG.KC.ThDemp.uAll (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.uAll CFSG.KC.ThDemp.uAll
  try rw [KC_ThDemp_stackN]
  try rw [KC_ThDemp_uVec]
  all_goals rfl

theorem KC_ThDemp_pow5 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.pow5 D =
      @CFSG.KC.ThDemp.pow5 (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.pow5 CFSG.KC.ThDemp.pow5
  try rw [KC_Th_BigS_powB]
  all_goals rfl

theorem KC_ThDemp_ordChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.ordChk D =
      @CFSG.KC.ThDemp.ordChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.ordChk CFSG.KC.ThDemp.ordChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_pow5]
  all_goals rfl

theorem KC_ThDemp_cent5 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.cent5 D =
      @CFSG.KC.ThDemp.cent5 (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.cent5 CFSG.KC.ThDemp.cent5
  try rw [KC_Loop_sumBelow]
  try rw [KC_ThDemp_DempData_T]
  try rw [KC_ThDemp_DempData_mul]
  all_goals rfl

theorem KC_ThDemp_rowAt : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.rowAt D =
      @CFSG.KC.ThDemp.rowAt (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.rowAt CFSG.KC.ThDemp.rowAt
  rfl

theorem KC_ThDemp_eqRows : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.eqRows D =
      @CFSG.KC.ThDemp.eqRows (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.eqRows CFSG.KC.ThDemp.eqRows
  try rw [KC_Loop_sumBelow]
  try rw [KC_ThDemp_rowAt]
  all_goals rfl

theorem KC_ThDemp_cycPt : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.cycPt D =
      @CFSG.KC.ThDemp.cycPt (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.cycPt CFSG.KC.ThDemp.cycPt
  try rw [KC_Loop_strictN]
  try rw [KC_Th_vecB]
  all_goals rfl

theorem KC_ThDemp_powStack : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.powStack D =
      @CFSG.KC.ThDemp.powStack (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.powStack CFSG.KC.ThDemp.powStack
  try rw [KC_Loop_strictN]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_DempData_S]
  try rw [KC_ThDemp_ptAt]
  try rw [KC_ThDemp_cR]
  all_goals rfl

theorem KC_ThDemp_qRows :
    @CFSGOutside.Corpus.Th.KC.ThDemp.qRows =
      @CFSG.KC.ThDemp.qRows := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.qRows CFSG.KC.ThDemp.qRows
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_ptAt]
  all_goals rfl

theorem KC_ThDemp_qCount :
    @CFSGOutside.Corpus.Th.KC.ThDemp.qCount =
      @CFSG.KC.ThDemp.qCount := by
  delta CFSGOutside.Corpus.Th.KC.ThDemp.qCount CFSG.KC.ThDemp.qCount
  try rw [KC_Loop_sumBelow]
  try rw [KC_ThDemp_qRows]
  all_goals rfl

theorem KC_ThDemp_wordM : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.wordM D =
      @CFSG.KC.ThDemp.wordM (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.wordM CFSG.KC.ThDemp.wordM
  try rw [KC_ThDemp_wordR]
  all_goals rfl

theorem KC_ThDemp_wordsChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.wordsChk D O =
      @CFSG.KC.ThDemp.wordsChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.wordsChk CFSG.KC.ThDemp.wordsChk
  try rw [KC_Th_andB]
  try rw [KC_Th_BigS_regBelow]
  all_goals rfl

theorem KC_ThDemp_codeChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.codeChk D =
      @CFSG.KC.ThDemp.codeChk (dempTo D) := by
  intro D
  delta CFSGOutside.Corpus.Th.KC.ThDemp.codeChk CFSG.KC.ThDemp.codeChk
  try rw [KC_Loop_allBelow]
  try rw [KC_Th_BigS_bitsN]
  try rw [KC_ThDemp_DempData_oszL]
  all_goals rfl

theorem KC_ThDemp_codesChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.codesChk D O =
      @CFSG.KC.ThDemp.codesChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.codesChk CFSG.KC.ThDemp.codesChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_codeChk]
  all_goals rfl

theorem KC_ThDemp_eltChk1 : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.eltChk1 D O =
      @CFSG.KC.ThDemp.eltChk1 (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.eltChk1 CFSG.KC.ThDemp.eltChk1
  try rw [KC_Th_andB]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_rowsOf]
  try rw [KC_ThDemp_combsL]
  try rw [KC_ThDemp_nodupB]
  try rw [KC_ThDemp_combChk]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_U0]
  try rw [KC_ThDemp_pt]
  try rw [KC_ThDemp_chainEl]
  try rw [KC_ThDemp_gen]
  try rw [KC_ThDemp_ordChk]
  try rw [KC_ThDemp_wordsChk]
  all_goals rfl

theorem KC_ThDemp_centChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.centChk D O =
      @CFSG.KC.ThDemp.centChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.centChk CFSG.KC.ThDemp.centChk
  try rw [KC_Th_andB]
  try rw [KC_Th_mulB]
  try rw [KC_Th_vecB]
  try rw [KC_ThDemp_DempData_bvL]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_combChk]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_U0]
  try rw [KC_ThDemp_chainEl]
  try rw [KC_ThDemp_uVec]
  try rw [KC_ThDemp_uAll]
  try rw [KC_ThDemp_cent5]
  try rw [KC_ThDemp_rowAt]
  try rw [KC_ThDemp_eqRows]
  try rw [KC_ThDemp_cycPt]
  all_goals rfl

theorem KC_ThDemp_qChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.qChk D O =
      @CFSG.KC.ThDemp.qChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.qChk CFSG.KC.ThDemp.qChk
  try rw [KC_Th_andB]
  try rw [KC_ThDemp_U0]
  try rw [KC_ThDemp_chainEl]
  try rw [KC_ThDemp_powStack]
  try rw [KC_ThDemp_qRows]
  try rw [KC_ThDemp_qCount]
  all_goals rfl

theorem KC_ThDemp_normChk : ∀ (D : CFSGOutside.Corpus.Th.KC.ThDemp.DempData) (O : CFSGOutside.Corpus.Th.KC.ThDemp.OrbData),
    @CFSGOutside.Corpus.Th.KC.ThDemp.normChk D O =
      @CFSG.KC.ThDemp.normChk (dempTo D) (orbTo O) := by
  intro D O
  delta CFSGOutside.Corpus.Th.KC.ThDemp.normChk CFSG.KC.ThDemp.normChk
  try rw [KC_Th_andB]
  try rw [KC_Th_mulB]
  try rw [KC_ThDemp_lgetL]
  try rw [KC_ThDemp_DempData_mul]
  try rw [KC_ThDemp_strictB]
  try rw [KC_ThDemp_keyL]
  try rw [KC_ThDemp_cR]
  try rw [KC_ThDemp_U0]
  try rw [KC_ThDemp_chainEl]
  try rw [KC_ThDemp_pow5]
  try rw [KC_ThDemp_wordM]
  all_goals rfl
end K

end CFSGOutsideClean.Corpus.Th
