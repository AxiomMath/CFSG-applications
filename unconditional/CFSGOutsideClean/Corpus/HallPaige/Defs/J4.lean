import CFSG.Sporadic.J4.F2Spec
import CFSG.Sporadic.J4.Local
import CFSG.Sporadic.Schreier.J4SLocal
import CFSGOutside.Corpus.HallPaige.J4

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.J4` are the corpus definitions.

The copied structure `V2` is a new type, so it is compared through the only value the classes use,
the root vector `rootV.toVec`.
-/

namespace CFSGOutsideClean.Corpus

theorem J4_asciiWhitespace_eq :
    @CFSGOutside.Corpus.J4.asciiWhitespace = @CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  with_unfolding_all rfl

theorem J4_decode_eq :
    @CFSGOutside.Corpus.J4.decode = @CFSG.Blueprint.NativeSporadic.decode := by
  with_unfolding_all rfl

theorem J4_seedMonoid_eq :
    @CFSGOutside.Corpus.J4.seedMonoid = @CFSG.Blueprint.NativeSporadic.seedMonoid := by
  with_unfolding_all rfl

theorem J4_J4Seed1_eq :
    @CFSGOutside.Corpus.J4.J4Seed1 = @CFSG.Blueprint.NativeSporadic.J4Seed1 := by
  with_unfolding_all rfl

theorem J4_J4Seed2_eq :
    @CFSGOutside.Corpus.J4.J4Seed2 = @CFSG.Blueprint.NativeSporadic.J4Seed2 := by
  with_unfolding_all rfl

theorem J4_J4_eq :
    @CFSGOutside.Corpus.J4.J4 = @CFSG.Blueprint.NativeSporadic.J4 := by
  with_unfolding_all rfl

theorem J4_matA_eq :
    @CFSGOutside.Corpus.J4.matA = @CFSG.Sporadic.J4.matA := by
  with_unfolding_all rfl

theorem J4_matB_eq :
    @CFSGOutside.Corpus.J4.matB = @CFSG.Sporadic.J4.matB := by
  with_unfolding_all rfl

theorem J4_wordProd_eq :
    @CFSGOutside.Corpus.J4.wordProd = @CFSG.Sporadic.J4.wordProd := by
  with_unfolding_all rfl

theorem J4_gA_eq :
    @CFSGOutside.Corpus.J4.gA = @CFSG.Sporadic.J4.gA := by
  with_unfolding_all rfl

theorem J4_gB_eq :
    @CFSGOutside.Corpus.J4.gB = @CFSG.Sporadic.J4.gB := by
  with_unfolding_all rfl

theorem J4_J_eq :
    @CFSGOutside.Corpus.J4.J = @CFSG.Sporadic.J4.J := by
  with_unfolding_all rfl

theorem J4_a_eq :
    @CFSGOutside.Corpus.J4.a = @CFSG.Sporadic.J4.a := by
  with_unfolding_all rfl

theorem J4_b_eq :
    @CFSGOutside.Corpus.J4.b = @CFSG.Sporadic.J4.b := by
  with_unfolding_all rfl

theorem J4_localWords_eq :
    @CFSGOutside.Corpus.J4.localWords = @CFSG.Sporadic.J4.Native.localWords := by
  with_unfolding_all rfl

theorem J4_baseGL_eq :
    @CFSGOutside.Corpus.J4.baseGL = @CFSG.Sporadic.J4.baseGL := by
  with_unfolding_all rfl

theorem J4_locGL_eq :
    @CFSGOutside.Corpus.J4.locGL = @CFSG.Sporadic.J4.locGL := by
  with_unfolding_all rfl

theorem J4_xJ_eq :
    @CFSGOutside.Corpus.J4.xJ = @CFSG.Sporadic.J4.xJ := by
  with_unfolding_all rfl

theorem J4_Hj_eq :
    @CFSGOutside.Corpus.J4.Hj = @CFSG.Sporadic.J4.Hj := by
  with_unfolding_all rfl

theorem J4_letterElt_eq :
    @CFSGOutside.Corpus.J4.letterElt = @CFSG.Sporadic.J4.QT2.letterElt := by
  with_unfolding_all rfl

/-- The copy is a separate structural recursion, so the two agree by induction, not by unfolding. -/
theorem J4_pathElt_eq :
    @CFSGOutside.Corpus.J4.pathElt = @CFSG.Sporadic.J4.QT2.pathElt := by
  funext p
  induction p with
  | nil => rfl
  | cons l ls ih =>
    rw [CFSGOutside.Corpus.J4.pathElt, CFSG.Sporadic.J4.QT2.pathElt, ih, J4_letterElt_eq]
    with_unfolding_all rfl

theorem J4_repPaths_eq :
    @CFSGOutside.Corpus.J4.repPaths = @CFSG.Sporadic.J4.QT2.repPaths := by
  with_unfolding_all rfl

theorem J4_Row_eq :
    @CFSGOutside.Corpus.J4.Row = @CFSG.Sporadic.J4.Row := by
  with_unfolding_all rfl

theorem J4_toRow_eq :
    @CFSGOutside.Corpus.J4.toRow = @CFSG.Sporadic.J4.toRow := by
  with_unfolding_all rfl

theorem J4_ofRow_eq :
    @CFSGOutside.Corpus.J4.ofRow = @CFSG.Sporadic.J4.ofRow := by
  with_unfolding_all rfl

theorem J4_rowAction_eq :
    @CFSGOutside.Corpus.J4.rowAction = @CFSG.Sporadic.J4.rowAction := by
  with_unfolding_all rfl

theorem J4_toVecD_eq :
    @CFSGOutside.Corpus.J4.toVecD = @CFSG.Sporadic.SmallF2.toVecD := by
  with_unfolding_all rfl

theorem J4_rootBits_eq :
    @CFSGOutside.Corpus.J4.rootBits = @CFSG.Sporadic.J4Schreier.rootBits := by
  with_unfolding_all rfl

theorem J4_v_eq :
    @CFSGOutside.Corpus.J4.v = @CFSG.Sporadic.J4Schreier.v := by
  with_unfolding_all rfl

theorem J4_rootV_toVec_eq :
    CFSGOutside.Corpus.J4.rootV.toVec = CFSG.Sporadic.J4.Native.rootV.toVec := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
