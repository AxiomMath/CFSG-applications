import CFSGOutside.GiuliettiKorchmaros.Theorem61
import CFSGOutsideClean.Corpus.MinimalNormalSimpleFactors
import CFSGOutsideClean.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutsideClean.Corpus.RankTwoSylowShapes
import CFSGOutsideClean.Corpus.UnitaryFourSylowStructure
import CFSGOutsideClean.Corpus.GorensteinWalterSimple
import CFSGOutsideClean.Corpus.LrSemidihedralSimpleRecognition
import CFSGOutsideClean.Corpus.SemilinearEquivAut
import CFSGOutsideClean.Corpus.AutAlternatingBijectiveConj
import CFSGOutsideClean.Corpus.M11AutInner
import CFSGOutsideClean.Corpus.QuaternionSylowStructure
import CFSGOutsideClean.Corpus.SpecialLinearGroupSylowQuaternion
import CFSGOutsideClean.Corpus.ThompsonTransferLemma

/-! Giulietti–Korchmáros (2019), Theorem 6.1 for odd core-free groups (group-theoretic form), with the 13 corpus
inputs supplied by the corpus. -/

namespace CFSGOutsideClean.GiuliettiKorchmaros

open CFSGOutside.GiuliettiKorchmaros

/-- **Automorphism groups of curves.** Let G be a finite group with no nontrivial normal subgroup of odd order, in which
every 2-subgroup has a cyclic subgroup of index at most 2. Then G has odd order, or is a 2-group, or its derived
subgroup is SL(2, q) with q odd and q ≥ 5, or G embeds in PΓL(2, q) with q odd and q ≥ 3 and contains PSL(2, q), or
G has a normal subgroup PSL(3, q) with q ≡ 3 (mod 4), or PSU(3, q) with q ≡ 1 (mod 4), whose centralizer is trivial,
or G is isomorphic to A₇, M₁₁, GL(2, 3), the binary octahedral group or SL(2, 3), or G is a perfect group of order
5040 whose quotient by its centre is A₇.

Source: M. Giulietti and G. Korchmáros, Algebraic curves with many automorphisms, Adv. Math. 349 (2019), 162–211,
Theorem 6.1. https://doi.org/10.1016/j.aim.2019.04.003 -/
theorem theorem_6_1 {G : Type} [Group G] [Finite G] (hP : CyclicIndexTwo G) (hO : OddCoreFree G) :
    Theorem61Conclusion G :=
  CFSGOutside.GiuliettiKorchmaros.theorem_6_1 hP hO

end CFSGOutsideClean.GiuliettiKorchmaros
