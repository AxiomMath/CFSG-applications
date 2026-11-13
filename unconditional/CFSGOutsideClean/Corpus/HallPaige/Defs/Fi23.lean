import CFSG.Blueprint.FischerDefs
import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.Fi23.SetupBase
import Certificates.Data.CFSGNative.Fi23.Data
import CFSGOutside.Corpus.HallPaige.Fi23

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.Fi23` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Fi23_asciiWhitespace_eq :
    @CFSGOutside.Corpus.Fi23.asciiWhitespace = @CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  with_unfolding_all rfl

theorem Fi23_decode_eq :
    @CFSGOutside.Corpus.Fi23.decode = @CFSG.Blueprint.NativeSporadic.decode := by
  with_unfolding_all rfl

theorem Fi23_seedMonoid_eq :
    @CFSGOutside.Corpus.Fi23.seedMonoid = @CFSG.Blueprint.NativeSporadic.seedMonoid := by
  with_unfolding_all rfl

theorem Fi23_Fi23Seed1_eq :
    @CFSGOutside.Corpus.Fi23.Fi23Seed1 = @CFSG.Blueprint.NativeSporadic.Fi23Seed1 := by
  with_unfolding_all rfl

theorem Fi23_Fi23Seed2_eq :
    @CFSGOutside.Corpus.Fi23.Fi23Seed2 = @CFSG.Blueprint.NativeSporadic.Fi23Seed2 := by
  with_unfolding_all rfl

theorem Fi23_Fi23_eq :
    @CFSGOutside.Corpus.Fi23.Fi23 = @CFSG.Blueprint.NativeSporadic.Fi23 := by
  with_unfolding_all rfl

theorem Fi23_unitSeedEquiv_eq :
    @CFSGOutside.Corpus.Fi23.unitSeedEquiv = @CFSG.Blueprint.NativeSporadic.unitSeedEquiv := by
  with_unfolding_all rfl

theorem Fi23_matrixSeedEquiv_eq :
    @CFSGOutside.Corpus.Fi23.matrixSeedEquiv = @CFSG.Blueprint.NativeSporadic.matrixSeedEquiv := by
  with_unfolding_all rfl

theorem Fi23_K_eq :
    @CFSGOutside.Corpus.Fi23.K = @CFSG.Blueprint.Fischer.K := by
  with_unfolding_all rfl

theorem Fi23_V_eq :
    @CFSGOutside.Corpus.Fi23.V = @CFSG.Blueprint.Fischer.V := by
  with_unfolding_all rfl

theorem Fi23_hermitian_eq :
    @CFSGOutside.Corpus.Fi23.hermitian = @CFSG.Blueprint.Fischer.hermitian := by
  with_unfolding_all rfl

theorem Fi23_IsNondegenerateHermitian_eq :
    @CFSGOutside.Corpus.Fi23.IsNondegenerateHermitian = @CFSG.Blueprint.Fischer.IsNondegenerateHermitian := by
  with_unfolding_all rfl

theorem Fi23_SU_eq :
    @CFSGOutside.Corpus.Fi23.SU = @CFSG.Blueprint.Fischer.SU := by
  with_unfolding_all rfl

theorem Fi23_PSU_eq :
    @CFSGOutside.Corpus.Fi23.PSU = @CFSG.Blueprint.Fischer.PSU := by
  with_unfolding_all rfl

theorem Fi23_Transvections_eq :
    @CFSGOutside.Corpus.Fi23.Transvections = @CFSG.Blueprint.Fischer.Transvections := by
  with_unfolding_all rfl

theorem Fi23_Pair_eq :
    @CFSGOutside.Corpus.Fi23.Pair = @CFSG.Blueprint.Fischer.Pair := by
  with_unfolding_all rfl

theorem Fi23_LocalClass_eq :
    @CFSGOutside.Corpus.Fi23.LocalClass = @CFSG.Blueprint.Fischer.LocalClass := by
  with_unfolding_all rfl

theorem Fi23_LocalGroup_eq :
    @CFSGOutside.Corpus.Fi23.LocalGroup = @CFSG.Blueprint.Fischer.LocalGroup := by
  with_unfolding_all rfl

theorem Fi23_LocalQuotient_eq :
    @CFSGOutside.Corpus.Fi23.LocalQuotient = @CFSG.Blueprint.Fischer.LocalQuotient := by
  with_unfolding_all rfl

theorem Fi23_LocalImages_eq :
    @CFSGOutside.Corpus.Fi23.LocalImages = @CFSG.Blueprint.Fischer.LocalImages := by
  with_unfolding_all rfl

theorem Fi23_F22_eq :
    @CFSGOutside.Corpus.Fi23.F22 = @CFSG.Blueprint.Fischer.F22 := by
  with_unfolding_all rfl

theorem Fi23_F23_eq :
    @CFSGOutside.Corpus.Fi23.F23 = @CFSG.Blueprint.Fischer.F23 := by
  with_unfolding_all rfl

theorem Fi23_mA_eq :
    @CFSGOutside.Corpus.Fi23.mA = @CFSG.Sporadic.Fi23.mA := by
  with_unfolding_all rfl

theorem Fi23_mB_eq :
    @CFSGOutside.Corpus.Fi23.mB = @CFSG.Sporadic.Fi23.mB := by
  with_unfolding_all rfl

theorem Fi23_dWord_eq :
    @CFSGOutside.Corpus.Fi23.dWord = @CFSG.Sporadic.Fi23.Native.dWord := by
  with_unfolding_all rfl

theorem Fi23_eWord_eq :
    @CFSGOutside.Corpus.Fi23.eWord = @CFSG.Sporadic.Fi23.Native.eWord := by
  with_unfolding_all rfl

theorem Fi23_genMat_eq :
    @CFSGOutside.Corpus.Fi23.genMat = @CFSG.Sporadic.Fi23.genMat := by
  with_unfolding_all rfl

theorem Fi23_mW_eq :
    @CFSGOutside.Corpus.Fi23.mW = @CFSG.Sporadic.Fi23.mW := by
  with_unfolding_all rfl

theorem Fi23_mE_eq :
    @CFSGOutside.Corpus.Fi23.mE = @CFSG.Sporadic.Fi23.mE := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
