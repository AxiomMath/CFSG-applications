import CFSG.Foundations.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSGOutside.Corpus.Defs.ElemThompson
import CFSGOutsideClean.Corpus.Defs.ElementaryAbelian

/-! The definitions copied into `CFSGOutside.Corpus.Defs.ElemThompson` are the corpus definitions. The copied
`p`-rank and Thompson subgroup are stated with the copied class `IsElementaryAbelian`, so they agree with the
corpus ones through `isElementaryAbelian_iff`. -/

namespace CFSGOutsideClean.Corpus

theorem pRank_eq (p : ℕ) (H : Type*) [Group H] :
    CFSGOutside.Corpus.pRank p H = CFSG.pRank p H := by
  unfold CFSGOutside.Corpus.pRank CFSG.pRank
  simp_rw [isElementaryAbelian_iff]

theorem elemThompsonFamily_eq (G : Type*) [Group G] (p : ℕ) :
    CFSGOutside.Corpus.elemThompsonFamily G p = CFSG.elemThompsonFamily G p := by
  unfold CFSGOutside.Corpus.elemThompsonFamily CFSG.elemThompsonFamily
  simp_rw [isElementaryAbelian_iff, pRank_eq]

theorem elemThompson_eq (G : Type*) [Group G] (p : ℕ) :
    CFSGOutside.Corpus.elemThompson G p = CFSG.elemThompson G p := by
  unfold CFSGOutside.Corpus.elemThompson CFSG.elemThompson
  rw [elemThompsonFamily_eq]

theorem hasNormalPComplement_iff (p : ℕ) (G : Type*) [Group G] :
    CFSGOutside.Corpus.HasNormalPComplement p G ↔ CFSG.HasNormalPComplement p G :=
  Iff.rfl

theorem isSylowOf_iff {G : Type*} [Group G] (p : ℕ) (P K : Subgroup G) :
    CFSGOutside.Corpus.ABGLocalTools.IsSylowOf p P K ↔ CFSG.ABGLocalTools.IsSylowOf p P K :=
  Iff.rfl

end CFSGOutsideClean.Corpus
