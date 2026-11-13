import Comparator.Solution
import CFSGOutside.HallPaige.Main
import CFSGOutsideClean.Corpus.HallPaige.Co1
import CFSGOutsideClean.Corpus.HallPaige.Co2
import CFSGOutsideClean.Corpus.HallPaige.Co3
import CFSGOutsideClean.Corpus.HallPaige.Fi22
import CFSGOutsideClean.Corpus.HallPaige.Fi23
import CFSGOutsideClean.Corpus.HallPaige.Fi24Prime
import CFSGOutsideClean.Corpus.HallPaige.HN
import CFSGOutsideClean.Corpus.HallPaige.LieExcChevalley
import CFSGOutsideClean.Corpus.HallPaige.LieExcTw
import CFSGOutsideClean.Corpus.HallPaige.LieExcTwRee
import CFSGOutsideClean.Corpus.HallPaige.LieOrth
import CFSGOutsideClean.Corpus.HallPaige.LieRankOneRee
import CFSGOutsideClean.Corpus.HallPaige.LieSuzuki
import CFSGOutsideClean.Corpus.HallPaige.LieSymplectic
import CFSGOutsideClean.Corpus.HallPaige.LieTypeA
import CFSGOutsideClean.Corpus.HallPaige.LieUnitary
import CFSGOutsideClean.Corpus.HallPaige.Mathieu
import CFSGOutsideClean.Corpus.HallPaige.McL
import CFSGOutsideClean.Corpus.HallPaige.ONan
import CFSGOutsideClean.Corpus.HallPaige.Ru
import CFSGOutsideClean.Corpus.HallPaige.SporadicOrder
import CFSGOutsideClean.Corpus.HallPaige.SporadicSimple
import CFSGOutsideClean.Corpus.HallPaige.Suz
import CFSGOutsideClean.Corpus.HallPaige.Tits
import CFSGOutsideClean.Corpus.HallPaige.B
import CFSGOutsideClean.Corpus.HallPaige.J4
import CFSGOutsideClean.Corpus.HallPaige.Ly
import CFSGOutsideClean.Corpus.HallPaige.M
import CFSGOutsideClean.Corpus.HallPaige.Th
import CFSGOutsideClean.Corpus.HallPaige.Defs.Co1
import CFSGOutsideClean.Corpus.HallPaige.Defs.Fi23
import CFSGOutsideClean.Corpus.HallPaige.Defs.LieOrth
import CFSGOutsideClean.Corpus.HallPaige.Defs.LieSuzuki
import CFSGOutsideClean.Corpus.HallPaige.Defs.LieSymplectic
import CFSGOutsideClean.Corpus.HallPaige.Defs.LieUnitary
import CFSGOutsideClean.Corpus.HallPaige.Defs.Mathieu
import CFSGOutsideClean.Corpus.HallPaige.Defs.Tits

/-!
# The Hall–Paige theorem

M. Hall and L. J. Paige, *Complete mappings of finite groups*, Pacific J. Math. 5 (1955), 541–549, proved the
necessity (their Theorem 5) and conjectured the converse: a finite group has a complete mapping if and only if its
Sylow `2`-subgroups are trivial or non-cyclic. The conjecture was proved by S. Wilcox (2009), A. B. Evans (2009) and
J. N. Bray et al. (2020). The classification statement is supplied by the corpus,
`CFSGComparator.classification`, and the corpus theorems the proof uses by the instances in
`CFSGOutsideClean.Corpus.HallPaige`.
-/

namespace CFSGOutsideClean.HallPaige

open CFSGOutside.HallPaige

universe u

/-- **Hall–Paige (1955), Theorem 5.** A finite group with a complete mapping satisfies the Hall–Paige condition:
its Sylow `2`-subgroups are trivial or non-cyclic. -/
theorem isGood_of_hasCompleteMapping {G : Type*} [Group G] [Finite G] (h : HasCompleteMapping G) : IsGood G :=
  CFSGOutside.HallPaige.isGood_of_hasCompleteMapping h

/-- **Hall–Paige conjecture.** A finite group G has a complete mapping, a bijection θ : G → G such that x ↦ x·θ(x) is
also a bijection, if and only if its Sylow 2-subgroups are trivial or non-cyclic.

Source: M. Hall and L. J. Paige, Complete mappings of finite groups, Pacific J. Math. 5 (1955), 541–549, Theorem 5
and the conjecture of §1; proved by S. Wilcox (2009), A. B. Evans (2009) and J. N. Bray, Q. Cai, P. J. Cameron, P.
Spiga, H. Zhang (2020). https://doi.org/10.2140/pjm.1955.5.541 -/
theorem hall_paige (G : Type u) [Group G] [Finite G] :
    HasCompleteMapping G ↔ IsGood G :=
  CFSGOutside.HallPaige.hall_paige CFSGComparator.classification.{0} G

end CFSGOutsideClean.HallPaige

#print axioms CFSGOutsideClean.HallPaige.hall_paige
#print axioms CFSGOutsideClean.HallPaige.isGood_of_hasCompleteMapping
