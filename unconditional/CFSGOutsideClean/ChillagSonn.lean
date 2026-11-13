import CFSGOutside.ChillagSonn.Theorem1
import CFSGOutsideClean.Corpus.SchurMultipliers
import CFSGOutsideClean.Corpus.MinimalNormalSimpleFactors
import CFSGOutsideClean.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutsideClean.Corpus.LrRankTwoIsomorphismTypes
import CFSGOutsideClean.Corpus.CardStatedProjStatedSL
import CFSGOutsideClean.Corpus.CardPsuThreeMulGcd
import CFSGOutsideClean.Corpus.FrattiniQuotientFacts
import CFSGOutsideClean.Corpus.FrobeniusNormalPComplement
import CFSGOutsideClean.Corpus.DicksonPsl2
import CFSGOutsideClean.Corpus.Gaschutz
import CFSGOutsideClean.Corpus.SemilinearEquivAut
import CFSGOutsideClean.Corpus.AutAlternatingBijectiveConj
import CFSGOutsideClean.Corpus.M11AutInner
import CFSGOutsideClean.Corpus.SolvableHall
import CFSGOutsideClean.Corpus.Defs.OddCoreDihedral
import CFSGOutsideClean.Corpus.Defs.DGroup
import CFSGOutsideClean.Corpus.Defs.PGammaL2
import CFSGOutsideClean.Corpus.Defs.StatedM11

/-! Chillag–Sonn (1981), Theorem 1 (the structure of finite Sylow-metacyclic groups), with the 22 corpus inputs
supplied by the corpus. The copied `oddCore`, `PSL2`, `PGL2`, `PGammaL2` and `StatedM11` in the statement are the
corpus definitions by `rfl`. -/

namespace CFSGOutsideClean.ChillagSonn

open CFSGOutside.ChillagSonn

/-- **Sylow-metacyclic groups.** Let G be a finite group all of whose Sylow subgroups are metacyclic. Then G = NA with N
a normal subgroup of odd order having a Sylow tower and N ∩ A = 1, and either (i) G is solvable and A is a Hall
{2,3}-subgroup, or (ii) N = O(G), every prime dividing both |A| and |N| has abelian Sylow subgroups in G and cyclic
ones in A and N, and either A = A′ is M₁₁, A₇, the double cover of A₇, PSL(2, pⁱ) or SL(2, pⁱ), with G = A × N
unless A ≅ SL(2, 5), or |A : A′| = 2, A is PGL(2, pⁱ), a double stem cover of it, or PGL*(2, p²), and |A : C_A(N)| ≤
2. Here p is prime, i ∈ {1, 2} and pⁱ ≥ 5.

Source: D. Chillag and J. Sonn, Sylow-metacyclic groups and Q-admissibility, Israel J. Math. 40 (1981), 307–323,
Theorem 1. https://doi.org/10.1007/BF02761371 -/
theorem theorem_1 {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) : Theorem1Conclusion G :=
  CFSGOutside.ChillagSonn.theorem_1 hG

end CFSGOutsideClean.ChillagSonn
