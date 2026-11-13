import CFSGOutside.ChillagSonn.Defs
import CFSGOutside.Corpus.SchurMultipliers
import CFSGOutside.Corpus.MinimalNormalSimpleFactors
import CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutside.Corpus.LrRankTwoIsomorphismTypes
import CFSGOutside.Corpus.CardStatedProjStatedSL
import CFSGOutside.Corpus.CardPsuThreeMulGcd
import CFSGOutside.Corpus.FrattiniQuotientFacts
import CFSGOutside.Corpus.FrobeniusNormalPComplement
import CFSGOutside.Corpus.DicksonPsl2
import CFSGOutside.Corpus.Gaschutz
import CFSGOutside.Corpus.SemilinearEquivAut
import CFSGOutside.Corpus.AutAlternatingBijectiveConj
import CFSGOutside.Corpus.M11AutInner
import CFSGOutside.Corpus.SolvableHall

/-!
# Chillag–Sonn (1981), Theorem 1 (fast path)

D. Chillag and J. Sonn, Israel J. Math. 40 (1981) 307–323, Theorem 1: the structure of a finite Sylow-metacyclic
group. Conditional on 22 corpus theorems stated as classes in `CFSGOutside.Corpus`. `SylowMetacyclic` and
`Theorem1Conclusion` are defined in `CFSGOutside.ChillagSonn.Defs`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter

theorem theorem_1 [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
    [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
    [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
    [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
    [DicksonPsl2SubgroupClassification.{0}] [Gaschutz.{0}] [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj]
    [M11AutInner] [SolvableHallExistence.{0}] [SolvableHallConjugacy.{0}]
    {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) : Theorem1Conclusion G := sorry

end CFSGOutside.ChillagSonn
