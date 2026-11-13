import CFSGOutside.GiuliettiKorchmaros.Thm61Defs
import CFSGOutside.Corpus.MinimalNormalSimpleFactors
import CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutside.Corpus.RankTwoSylowShapes
import CFSGOutside.Corpus.UnitaryFourSylowStructure
import CFSGOutside.Corpus.GorensteinWalterSimple
import CFSGOutside.Corpus.LrSemidihedralSimpleRecognition
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutside.Corpus.AutAlternatingBijectiveConj
import CFSGOutside.Corpus.M11AutInner
import CFSGOutside.Corpus.QuaternionSylowStructure
import CFSGOutside.Corpus.SpecialLinearGroupSylowQuaternion
import CFSGOutside.Corpus.ThompsonTransferLemma

/-!
# Giulietti–Korchmáros (2019), Theorem 6.1, odd core-free case (fast path)

M. Giulietti, G. Korchmáros, Adv. Math. 349 (2019) 162–211, Theorem 6.1 for `O(G) = 1`, group-theoretic form.
Conditional on 13 corpus theorems stated as classes in `CFSGOutside.Corpus`. `CyclicIndexTwo`, `OddCoreFree` and
`Theorem61Conclusion` are defined in `CFSGOutside.GiuliettiKorchmaros.Defs` and `.Thm61Defs`.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus

theorem theorem_6_1 {G : Type} [Group G] [Finite G] [MinimalNormalSimpleFactors.{0}]
    [TwoLePRankOfIsSimpleGroup.{0}] [RankTwoSylowShapes] [UnitaryFourSylowStructure] [GorensteinWalterSimple] [LrSemidihedralSimpleRecognition]
    [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj] [M11AutInner] [NativeM11EquivOpen]
    [QuaternionSylowStructure.{0}] [SpecialLinearGroupSylowQuaternion.{0}] [ThompsonTransferLemma.{0}]
    (hP : CyclicIndexTwo G) (hO : OddCoreFree G) : Theorem61Conclusion G := sorry

end CFSGOutside.GiuliettiKorchmaros
