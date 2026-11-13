import CFSGOutside.HallPaige.CatalogueDefs
import CFSGOutside.HallPaige.Cases
import CFSGOutside.HallPaige.LieCases
import CFSGOutside.HallPaige.Necessity
import CFSGOutside.HallPaige.CentralTwo
import CFSGOutside.HallPaige.IndexTwo
import CFSGOutside.HallPaige.Reduction

/-!
# The Hall–Paige theorem (conditional version)

The theorem, assuming the classification of finite simple groups (`hCFSG`) and the corpus theorems
stated as classes in `CFSGOutside.Corpus`. Every catalogue case is proved.
-/

namespace CFSGOutside.HallPaige

open TauCeti

universe u

/-- Sufficiency for all finite groups, from the classification and the catalogue cases. -/
theorem hasCompleteMapping_of_isGood_of_catalogue (hCFSG : ClassificationStatement.{0})
    (hcat : ∀ i, CatalogueCase i) (G : Type u) [Group G] [Finite G] (hG : IsGood G) :
    HasCompleteMapping G :=
  hasCompleteMapping_of_isGood_of_simple'
    (fun N _ hN hQ => hasCompleteMapping_of_normal N hN hQ)
    (fun hG N _ hN hQ => hasCompleteMapping_of_normal_card_two hG N hN hQ)
    (fun hG N _ hidx hN => hasCompleteMapping_of_index_two hG N hidx hN)
    (fun G _ _ hs hG hP => simple_case_of_catalogue hCFSG hcat G hs hG hP) G hG

section
variable [h0 : Corpus.Co1.Orbits] [h1 : Corpus.Co2.FiniteCardLe] [h2 : Corpus.Co3.FiniteCardLe] [h3 : Corpus.Fi22.FiniteCardLe] [h4 : Corpus.Fi23.Setup] [h5 : Corpus.Fi23.Theorems] [h6 : Corpus.Fi24Prime.FiniteCardLe] [h7 : Corpus.HN.FiniteCardLe] [h8 : Corpus.Mathieu.Bridges] [h9 : Corpus.McL.FiniteCardLe] [h10 : Corpus.ONan.FiniteCardLe] [h11 : Corpus.Ru.FiniteCardLe] [h12 : Corpus.Bounds] [h13 : Corpus.Simple] [h14 : Corpus.Suz.FiniteCardLe] [h15 : Corpus.J4.Bridge] [h16 : Corpus.J4.Cover] [h17 : Corpus.J4.Stab] [h18 : Corpus.Ly.Theorems] [h19 : Corpus.Th.Theorems] [h20 : Corpus.Th.Generic.{0, 0}] [h21 : Corpus.B.Theorems] [h22 : Corpus.M.Theorems]
include h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22

theorem catalogueCase_sporadic (s : SporadicName) :
    CatalogueCase (.sporadic s) := by
  cases s
  all_goals first
    | exact catalogueCase_M11 | exact catalogueCase_M12 | exact catalogueCase_M22
    | exact catalogueCase_M23 | exact catalogueCase_M24 | exact catalogueCase_J1
    | exact catalogueCase_J2 | exact catalogueCase_J3 | exact catalogueCase_HS
    | exact catalogueCase_McL | exact catalogueCase_He | exact catalogueCase_Ru
    | exact catalogueCase_Suz | exact catalogueCase_Co1 | exact catalogueCase_Co2
    | exact catalogueCase_Co3 | exact catalogueCase_Fi22 | exact catalogueCase_Fi23 | exact catalogueCase_ONan
    | exact catalogueCase_Fi24Prime | exact catalogueCase_HN | exact catalogueCase_Ly
    | exact catalogueCase_J4 | exact catalogueCase_Th | exact catalogueCase_B
    | exact catalogueCase_M

end

/-- **Hall–Paige conjecture.** A finite group G has a complete mapping, a bijection θ : G → G such that x ↦ x·θ(x) is
also a bijection, if and only if its Sylow 2-subgroups are trivial or non-cyclic.

Source: M. Hall and L. J. Paige, Complete mappings of finite groups, Pacific J. Math. 5 (1955), 541–549, Theorem 5
and the conjecture of §1; proved by S. Wilcox (2009), A. B. Evans (2009) and J. N. Bray, Q. Cai, P. J. Cameron, P.
Spiga, H. Zhang (2020). https://doi.org/10.2140/pjm.1955.5.541

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
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
    [Corpus.Tits.Theorems] (hCFSG : ClassificationStatement.{0}) 
    (G : Type u) [Group G] [Finite G] :
    HasCompleteMapping G ↔ IsGood G := by
  refine ⟨isGood_of_hasCompleteMapping, hasCompleteMapping_of_isGood_of_catalogue hCFSG ?_ G⟩
  rintro (⟨p, hp⟩ | ⟨n, hn⟩ | d | s)
  · exact catalogueCase_cyclic p hp
  · exact catalogueCase_alternating n hn
  · exact catalogueCase_lie d
  · exact catalogueCase_sporadic s

end CFSGOutside.HallPaige
