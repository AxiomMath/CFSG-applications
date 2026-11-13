import CFSG.Blueprint.NativeSporadic
import CFSGOutside.Corpus.HallPaige.Mathieu

/-! The definitions copied into `CFSGOutside.Corpus.HallPaige.Mathieu` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus

theorem Mathieu_M11_eq :
    @CFSGOutside.Corpus.Mathieu.M11 = @CFSG.Blueprint.NativeSporadic.M11 := by
  with_unfolding_all rfl

theorem Mathieu_M12_eq :
    @CFSGOutside.Corpus.Mathieu.M12 = @CFSG.Blueprint.NativeSporadic.M12 := by
  with_unfolding_all rfl

theorem Mathieu_M22_eq :
    @CFSGOutside.Corpus.Mathieu.M22 = @CFSG.Blueprint.NativeSporadic.M22 := by
  with_unfolding_all rfl

theorem Mathieu_M23_eq :
    @CFSGOutside.Corpus.Mathieu.M23 = @CFSG.Blueprint.NativeSporadic.M23 := by
  with_unfolding_all rfl

theorem Mathieu_M24_eq :
    @CFSGOutside.Corpus.Mathieu.M24 = @CFSG.Blueprint.NativeSporadic.M24 := by
  with_unfolding_all rfl

end CFSGOutsideClean.Corpus
