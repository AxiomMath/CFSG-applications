import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSGOutside.Corpus.AlperinFusion

/-! The corpus proves the statement that `CFSGOutside.Corpus.AlperinFusion` assumes.

`IsAlperinSubgroup` is copied verbatim, so it is the corpus definition. `AlperinDecomposition` is an inductive
copy, so a corpus decomposition is mapped to a copied one constructor by constructor. -/

namespace CFSGOutsideClean.Corpus

theorem isAlperinSubgroup_iff {G : Type*} [Group G] (p : ℕ) (S Q : Subgroup G) :
    CFSGOutside.Corpus.IsAlperinSubgroup p S Q ↔ CFSG.RankTwoShapes.IsAlperinSubgroup p S Q :=
  Iff.rfl

theorem alperinDecomposition_of_corpus {G : Type*} [Group G] {p : ℕ} {S P : Subgroup G} {c : G}
    (h : CFSG.RankTwoShapes.AlperinDecomposition p S P c) :
    CFSGOutside.Corpus.AlperinDecomposition p S P c := by
  induction h with
  | one => exact .one
  | step _ hQ hPQ hn ih => exact .step ih hQ hPQ hn

instance alperinFusion : CFSGOutside.Corpus.AlperinFusion :=
  ⟨by
    intro _ _ _ _ _ S _ hP _ hg
    obtain ⟨c, hc, hx⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hP hg
    exact ⟨c, alperinDecomposition_of_corpus hc, hx⟩⟩

end CFSGOutsideClean.Corpus
