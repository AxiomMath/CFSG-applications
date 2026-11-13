import CFSGOutside.Corpus.HallPaige.Co1
import CFSGOutside.Corpus.HallPaige.Co2
import CFSGOutside.Corpus.HallPaige.Co3
import CFSGOutside.Corpus.HallPaige.Fi22
import CFSGOutside.Corpus.HallPaige.Fi23
import CFSGOutside.Corpus.HallPaige.Fi24Prime
import CFSGOutside.Corpus.HallPaige.HN
import CFSGOutside.Corpus.HallPaige.J4
import CFSGOutside.Corpus.HallPaige.LieExcChevalley
import CFSGOutside.Corpus.HallPaige.LieExcTw
import CFSGOutside.Corpus.HallPaige.LieExcTwRee
import CFSGOutside.Corpus.HallPaige.LieOrth
import CFSGOutside.Corpus.HallPaige.LieRankOneRee
import CFSGOutside.Corpus.HallPaige.LieSuzuki
import CFSGOutside.Corpus.HallPaige.LieSymplectic
import CFSGOutside.Corpus.HallPaige.LieTypeA
import CFSGOutside.Corpus.HallPaige.LieUnitary
import CFSGOutside.Corpus.HallPaige.B
import CFSGOutside.Corpus.HallPaige.Ly
import CFSGOutside.Corpus.HallPaige.M
import CFSGOutside.Corpus.HallPaige.Mathieu
import CFSGOutside.Corpus.HallPaige.McL
import CFSGOutside.Corpus.HallPaige.ONan
import CFSGOutside.Corpus.HallPaige.Ru
import CFSGOutside.Corpus.HallPaige.SporadicOrder
import CFSGOutside.Corpus.HallPaige.SporadicSimple
import CFSGOutside.Corpus.HallPaige.Suz
import CFSGOutside.Corpus.HallPaige.Th
import CFSGOutside.Corpus.HallPaige.Tits
import CFSGOutside.HallPaige.CatalogueDefs

/-!
# The Hall–Paige theorem (fast path)

P. Hall and L. J. Paige, *Complete mappings of finite groups*, Pacific J. Math. 5 (1955), 541–549, proved the
necessity (their Theorem 5) and conjectured the converse: a finite group has a complete mapping if and only if its
Sylow `2`-subgroups are trivial or non-cyclic. The conjecture was proved by S. Wilcox (2009), A. B. Evans (2009) and
J. N. Bray et al. (2020).

Conditional on the classification statement `TauCeti.ClassificationStatement` and on the corpus theorems stated as
classes in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.HallPaige

universe u

/-- **Hall–Paige (1955), Theorem 5.** A finite group with a complete mapping satisfies the Hall–Paige condition:
its Sylow `2`-subgroups are trivial or non-cyclic. No corpus input is needed. -/
theorem isGood_of_hasCompleteMapping {G : Type*} [Group G] [Finite G] (h : HasCompleteMapping G) : IsGood G := sorry

/-- **Hall–Paige theorem** (conditional on the classification and on the corpus theorems stated as classes): a finite
group has a complete mapping iff its Sylow `2`-subgroups are trivial or non-cyclic. -/
theorem hall_paige
    [Corpus.Exc.RootPred]
    [Corpus.Exc.Ops]
    [Corpus.ExcTw.LabelPerm]
    [Corpus.Ree.ReeTag.ReeAut]
    [Corpus.Co1.Orbits]
    [Corpus.Co2.FiniteCardLe]
    [Corpus.Co3.FiniteCardLe]
    [Corpus.Fi22.FiniteCardLe]
    [Corpus.Fi23.Setup]
    [Corpus.Fi23.Theorems]
    [Corpus.Fi24Prime.FiniteCardLe]
    [Corpus.HN.FiniteCardLe]
    [Corpus.J4.Bridge]
    [Corpus.J4.Cover]
    [Corpus.J4.Stab]
    [Corpus.Ly.Theorems]
    [Corpus.Th.Theorems]
    [Corpus.Th.Generic.{0, 0}]
    [Corpus.B.Theorems]
    [Corpus.M.Theorems]
    [Corpus.Exc.ParameterAddition]
    [Corpus.Exc.Liftable]
    [Corpus.Exc.Descent]
    [Corpus.Exc.BorelNormal]
    [Corpus.Exc.Chevalley]
    [Corpus.Exc.TorusElt]
    [Corpus.Exc.SylowTwo]
    [Corpus.Exc.Bridges]
    [Corpus.ExcTw.GraphFixed]
    [Corpus.ExcTw.Bridges]
    [Corpus.Ree.FiniteWeylGroup]
    [Corpus.Ree.ReeTag.FixedOrbits]
    [Corpus.Ree.ReeGammaCat]
    [Corpus.Lie.OrthEquivs]
    [Corpus.Ree.ReeModel]
    [Corpus.Lie.SuzukiOmega]
    [Corpus.Lie.SuzukiOvoid]
    [Corpus.Lie.SymplecticEquivs]
    [Corpus.Lie.TypeAEquiv]
    [Corpus.Lie.UnitaryEquiv]
    [Corpus.Mathieu.Bridges]
    [Corpus.McL.FiniteCardLe]
    [Corpus.ONan.FiniteCardLe]
    [Corpus.Ru.FiniteCardLe]
    [Corpus.Bounds]
    [Corpus.Simple]
    [Corpus.Suz.FiniteCardLe]
    [Corpus.Tits.Theorems]
    (hCFSG : TauCeti.ClassificationStatement.{0}) (G : Type u) [Group G] [Finite G] :
    HasCompleteMapping G ↔ IsGood G := sorry

end CFSGOutside.HallPaige
