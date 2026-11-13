import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.SchreierChainData
import CFSG.LieType.SeitzGeneration.Defs
import CFSG.Monster.B.Co2.PermArr
import CFSG.Sporadic.Schreier.TitsArrays
import CFSG.Sporadic.Schreier.TitsBasic
import CFSG.Sporadic.Schreier.TitsCert
import CFSG.Sporadic.Schreier.TitsCertCheckInputs
import CFSG.Sporadic.Schreier.TitsData
import CFSG.Sporadic.Schreier.TitsLocal
import CFSG.Sporadic.Schreier.TitsStab
import Certificates.Data.CFSGNative.MonsterB.Co2Data
import Certificates.Data.Kernel.Spor.Chain
import Certificates.Kernel.Misc.Tits.Text
import CFSGOutside.Corpus.HallPaige.Tits

/-! The copied definitions are the corpus ones. The generator `Tab.*` (the corpus code that produces the packed table `TitsText.F`)
is not compared: its output `TitsText.F` is (`TitsText_F_eq`). Some corpus definitions are irreducible. -/

attribute [local semireducible] CFSGOutside.Corpus.Tits.permOfArr CFSGOutside.Corpus.Tits.titsArr1755
  CFSG.Monster.B.Co2.permOfArr CFSG.Sporadic.Schreier.Tits.titsArr1755

namespace CFSGOutsideClean.Corpus

theorem TitsText_F_eq :
    CFSGOutside.Corpus.Tits.TitsText.F = CertificateChecks.KernelMisc.TitsText.F := by
  with_unfolding_all rfl

theorem Tits_hexVal_eq :
    @CFSGOutside.Corpus.Tits.hexVal = @CFSG.Monster.B.Co2.Native.hexVal := by
  with_unfolding_all rfl

theorem Tits_hexAt_eq :
    @CFSGOutside.Corpus.Tits.hexAt = @CFSG.Monster.B.Co2.Native.hexAt := by
  funext b o w
  induction w with
  | zero => rfl
  | succ w ih =>
    show CFSGOutside.Corpus.Tits.hexAt b o w * 16 + _ = CFSG.Monster.B.Co2.Native.hexAt b o w * 16 + _
    rw [ih]; rfl

theorem Tits_Rep_eq :
    @CFSGOutside.Corpus.Tits.Rep = @CFSG.Monster.B.Co2.Rep := by
  with_unfolding_all rfl

theorem Tits_permOfArr_eq :
    @CFSGOutside.Corpus.Tits.permOfArr = @CFSG.Monster.B.Co2.permOfArr := by
  with_unfolding_all rfl

theorem Tits_SchreierLetter_eq :
    @CFSGOutside.Corpus.Tits.SchreierLetter = @CFSG.Certificates.SchreierLetter := by
  with_unfolding_all rfl

theorem Tits_toLetters_eq :
    @CFSGOutside.Corpus.Tits.toLetters = @CFSG.Monster.B.Co2.toLetters := by
  with_unfolding_all rfl

theorem Tits_wordIn_eq :
    @CFSGOutside.Corpus.Tits.wordIn = @CFSG.Sporadic.Schreier.Tits.wordIn := by
  with_unfolding_all rfl

theorem Tits_tcomm_eq :
    @CFSGOutside.Corpus.Tits.tcomm = @CFSG.Sporadic.Schreier.Tits.tcomm := by
  with_unfolding_all rfl

theorem Tits_mask_eq :
    @CFSGOutside.Corpus.Tits.mask = @CFSG.KS.mask := by
  with_unfolding_all rfl

theorem Tits_pg_eq :
    @CFSGOutside.Corpus.Tits.pg = @CFSG.KC.Enum.pg := by
  with_unfolding_all rfl

theorem Tits_unpack_eq :
    @CFSGOutside.Corpus.Tits.unpack = @CFSG.KS.Raw.unpack := by
  with_unfolding_all rfl

theorem Tits_titsPerm1755Text_eq :
    @CFSGOutside.Corpus.Tits.titsPerm1755Text = @CFSG.Sporadic.Schreier.Tits.titsPerm1755Text := by
  with_unfolding_all rfl

theorem Tits_titsDerivedComm_eq :
    @CFSGOutside.Corpus.Tits.titsDerivedComm = @CFSG.Sporadic.Schreier.Tits.titsDerivedComm := by
  with_unfolding_all rfl

theorem Tits_titsHWords_eq :
    @CFSGOutside.Corpus.Tits.titsHWords = @CFSG.Sporadic.Schreier.Tits.titsHWords := by
  with_unfolding_all rfl

theorem Tits_titsBytes1755_eq :
    @CFSGOutside.Corpus.Tits.titsBytes1755 = @CFSG.Sporadic.Schreier.Tits.titsBytes1755 := by
  with_unfolding_all rfl

theorem Tits_titsArr1755_eq :
    @CFSGOutside.Corpus.Tits.titsArr1755 = @CFSG.Sporadic.Schreier.Tits.titsArr1755 := by
  with_unfolding_all rfl

theorem Tits_titsField1755_eq :
    @CFSGOutside.Corpus.Tits.titsField1755 = @CFSG.Sporadic.Schreier.Tits.titsField1755 := by
  with_unfolding_all rfl

theorem Tits_titsGenArrs_eq :
    @CFSGOutside.Corpus.Tits.titsGenArrs = @CFSG.Sporadic.Schreier.Tits.titsGenArrs := by
  with_unfolding_all rfl

theorem Tits_titsDerivedArrs_eq :
    @CFSGOutside.Corpus.Tits.titsDerivedArrs = @CFSG.Sporadic.Schreier.Tits.titsDerivedArrs := by
  with_unfolding_all rfl

theorem Tits_titsU_eq :
    @CFSGOutside.Corpus.Tits.titsU = @CFSG.Sporadic.Schreier.Tits.titsU := by
  with_unfolding_all rfl

theorem Tits_titsV_eq :
    @CFSGOutside.Corpus.Tits.titsV = @CFSG.Sporadic.Schreier.Tits.titsV := by
  with_unfolding_all rfl

theorem Tits_titsGen_eq :
    @CFSGOutside.Corpus.Tits.titsGen = @CFSG.Sporadic.Schreier.Tits.titsGen := by
  with_unfolding_all rfl

theorem Tits_titsDGen_eq :
    @CFSGOutside.Corpus.Tits.titsDGen = @CFSG.Sporadic.Schreier.Tits.titsDGen := by
  with_unfolding_all rfl

theorem Tits_titsD_eq :
    @CFSGOutside.Corpus.Tits.titsD = @CFSG.Sporadic.Schreier.Tits.titsD := by
  with_unfolding_all rfl

theorem Tits_titsT_eq :
    @CFSGOutside.Corpus.Tits.titsT = @CFSG.Sporadic.Schreier.Tits.titsT := by
  with_unfolding_all rfl

theorem Tits_titsWordGroup_eq :
    @CFSGOutside.Corpus.Tits.titsWordGroup = @CFSG.Sporadic.Schreier.Tits.titsWordGroup := by
  with_unfolding_all rfl

theorem Tits_titsH_eq :
    @CFSGOutside.Corpus.Tits.titsH = @CFSG.Sporadic.Schreier.Tits.titsH := by
  with_unfolding_all rfl

theorem Tits_titsPointStab_eq :
    @CFSGOutside.Corpus.Tits.titsPointStab = @CFSG.Sporadic.Schreier.Tits.titsPointStab := by
  with_unfolding_all rfl

theorem Tits_Cat_eq :
    @CFSGOutside.Corpus.Tits.Cat = @CFSG.LieType.SeitzGeneration.Cat := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
