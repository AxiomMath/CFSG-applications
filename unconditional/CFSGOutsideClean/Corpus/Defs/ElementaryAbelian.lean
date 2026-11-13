import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSGOutside.Corpus.Defs.ElementaryAbelian

/-! The class copied into `CFSGOutside.Corpus.Defs.ElementaryAbelian` is the corpus class. -/

universe u

namespace CFSGOutsideClean.Corpus

theorem isElementaryAbelian_iff (p : ℕ) (G : Type u) [Group G] :
    CFSGOutside.Corpus.IsElementaryAbelian p G ↔ CFSG.IsElementaryAbelian p G :=
  ⟨fun h => { toIsMulCommutative := h.toIsMulCommutative, exponent_dvd_p := h.exponent_dvd_p },
    fun h => { toIsMulCommutative := h.toIsMulCommutative, exponent_dvd_p := h.exponent_dvd_p }⟩

end CFSGOutsideClean.Corpus
