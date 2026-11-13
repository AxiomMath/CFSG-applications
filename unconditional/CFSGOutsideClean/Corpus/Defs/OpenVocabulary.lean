import CFSG.Open.Defs
import CFSG.Open.LocalVocabulary
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSGOutside.Corpus.Defs.OpenVocabulary

/-! The definitions copied into `CFSGOutside.Corpus.Defs.OpenVocabulary` are the corpus definitions. -/

namespace CFSGOutsideClean.Corpus.Open

theorem isElemAbelian_iff (p : ℕ) {G : Type*} [Group G] (E : Subgroup G) :
    CFSGOutside.Corpus.Open.IsElemAbelian p E ↔ CFSG.Open.IsElemAbelian p E :=
  Iff.rfl

theorem pRank_eq (p : ℕ) {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    CFSGOutside.Corpus.Open.pRank p H = CFSG.Open.pRank p H :=
  rfl

theorem isCatalogGroup_iff (H : Type*) [Group H] :
    CFSGOutside.Corpus.Open.IsCatalogGroup H ↔ CFSG.Open.IsCatalogGroup H :=
  Iff.rfl

end CFSGOutsideClean.Corpus.Open

theorem CFSGOutsideClean.Corpus.i_7_13_1_pPrime_iff :
    CFSGOutside.Corpus.I_7_13_1_pPrime ↔
      CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime :=
  Iff.rfl
