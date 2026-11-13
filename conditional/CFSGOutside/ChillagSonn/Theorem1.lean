import CFSGOutside.ChillagSonn.Theorem1Case2

/-!
# Theorem 1 of Chillag–Sonn

D. Chillag and J. Sonn, *Sylow-metacyclic groups and Q-admissibility*, Israel J. Math. 40 (1981), 307–323,
Theorem 1: a finite Sylow-metacyclic group `G` is `G = N A`, `N ⊴ G` of odd order with a Sylow tower, `N ∩ A = 1`,
and either (i) `G` is solvable and `A` is a Hall subgroup of order `2ᵃ3ᵇ`, or (ii) `N = O(G)`, a prime dividing
`|A|` and `|N|` has abelian Sylow subgroups in `G` and cyclic ones in `A` and `N`, and `A` is one of `M₁₁`, `A₇`,
`Ã₇`, `PSL(2, pⁱ)`, `SL(2, pⁱ)` (with `G = A × N` unless `A ≅ SL(2, 5)`) or one of `PGL(2, pⁱ)`, `PGL(2, pⁱ)^±`,
`PGL*(2, p²)` (with `|A : C_A(N)| ≤ 2`), `i ≤ 2`, `pⁱ ≥ 5`.

The published results used without proof enter as the hypotheses (classes) of the statement; see
a generator script for their provenance.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter

/-- **Sylow-metacyclic groups.** Let G be a finite group all of whose Sylow subgroups are metacyclic. Then G = NA with N
a normal subgroup of odd order having a Sylow tower and N ∩ A = 1, and either (i) G is solvable and A is a Hall
{2,3}-subgroup, or (ii) N = O(G), every prime dividing both |A| and |N| has abelian Sylow subgroups in G and cyclic
ones in A and N, and either A = A′ is M₁₁, A₇, the double cover of A₇, PSL(2, pⁱ) or SL(2, pⁱ), with G = A × N
unless A ≅ SL(2, 5), or |A : A′| = 2, A is PGL(2, pⁱ), a double stem cover of it, or PGL*(2, p²), and |A : C_A(N)| ≤
2. Here p is prime, i ∈ {1, 2} and pⁱ ≥ 5.

Source: D. Chillag and J. Sonn, Sylow-metacyclic groups and Q-admissibility, Israel J. Math. 40 (1981), 307–323,
Theorem 1. https://doi.org/10.1007/BF02761371

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_1 [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
    [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
    [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
    [DicksonPsl2SubgroupClassification.{0}] [Gaschutz.{0}] [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj]
    [M11AutInner] [SolvableHallExistence.{0}] [SolvableHallConjugacy.{0}]
    {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) : Theorem1Conclusion G := by
  by_cases hs : Group.IsSolvable G
  · exact theorem_1_solvable hG hs
  by_cases hsimp : IsSimpleGroup (G ⧸ solvableRadical G)
  · exact theorem_1_case1 hG hs hsimp
  · exact theorem_1_case2 hG hs hsimp

end CFSGOutside.ChillagSonn
