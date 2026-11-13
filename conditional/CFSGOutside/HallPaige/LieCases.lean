import CFSGOutside.HallPaige.SporadicCases
import CFSGOutside.HallPaige.Lie.Suzuki
import CFSGOutside.HallPaige.Lie.SymplecticCase
import CFSGOutside.HallPaige.Lie.UnitaryCatalogue
import CFSGOutside.HallPaige.Lie.RankOneCase
import CFSGOutside.HallPaige.Lie.RankOneSU3Case
import CFSGOutside.HallPaige.Lie.OrthB2
import CFSGOutside.HallPaige.Lie.OrthCase
import CFSGOutside.HallPaige.Lie.ExcCase
import CFSGOutside.HallPaige.Lie.RankOneReeCase
import CFSGOutside.HallPaige.Lie.ExcTwCase
import CFSGOutside.HallPaige.Lie.ExcTwRee

/-!
# The Lie-type catalogue cases

Every Lie-type entry of the classification list, including the Tits group.
-/

namespace CFSGOutside.HallPaige

open TauCeti

section
variable [h0 : Corpus.Exc.RootPred] [h1 : Corpus.Exc.Ops] [h2 : Corpus.ExcTw.LabelPerm] [h3 : Corpus.Ree.ReeTag.ReeAut] [h4 : Corpus.Exc.ParameterAddition] [h5 : Corpus.Exc.Liftable] [h6 : Corpus.Exc.Descent] [h7 : Corpus.Exc.BorelNormal] [h8 : Corpus.Exc.Chevalley] [h9 : Corpus.Exc.TorusElt] [h10 : Corpus.Exc.SylowTwo] [h11 : Corpus.Exc.Bridges] [h12 : Corpus.ExcTw.GraphFixed] [h13 : Corpus.ExcTw.Bridges] [h14 : Corpus.Ree.FiniteWeylGroup] [h15 : Corpus.Ree.ReeTag.FixedOrbits] [h16 : Corpus.Ree.ReeGammaCat] [h17 : Corpus.Lie.OrthEquivs] [h18 : Corpus.Ree.ReeModel] [h19 : Corpus.Lie.SuzukiOmega] [h20 : Corpus.Lie.SuzukiOvoid] [h21 : Corpus.Lie.SymplecticEquivs] [h22 : Corpus.Lie.TypeAEquiv] [h23 : Corpus.Lie.UnitaryEquiv] [h24 : Corpus.Simple] [h25 : Corpus.Tits.Theorems]
include h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25

theorem catalogueCase_lie (d : ValidLieTypeIndex) : CatalogueCase (.lie d) := by
  obtain ⟨d, hv⟩ := d
  have hr := hv.1
  cases d with
  | A r q => exact catalogueCase_A_all r q hv
  | twistedA r q =>
    rcases (show 2 ≤ r from hr.1).eq_or_lt with rfl | h
    · exact catalogueCase_twistedA_two q hv
    · exact catalogueCase_twistedA r q hv h
  | B r q =>
    rcases (show 2 ≤ r from hr.1).eq_or_lt with rfl | h
    · by_cases hq : q.p = 2
      · exact catalogueCase_B2_even q hv hq
      · exact catalogueCase_B2_odd q hv hq
    · by_cases hq : q.p = 2
      · exact catalogueCase_B_even r q hv hq h
      · exact catalogueCase_B_odd r q hv hq h
  | C r q => exact catalogueCase_C r q hv
  | D r q => exact catalogueCase_D r q hv
  | twistedD r q => exact catalogueCase_twistedD r q hv
  | E6 q => exact Exc.catalogueCase_E6 q hv
  | E7 q => exact Exc.catalogueCase_E7 q hv
  | E8 q => exact Exc.catalogueCase_E8 q hv
  | F4 q => exact Exc.catalogueCase_F4 q hv
  | G2 q => exact Exc.catalogueCase_G2 q hv
  | twistedE6 q => exact ExcTw.catalogueCase_twistedE6 q hv
  | trialityD4 q => exact ExcTw.catalogueCase_trialityD4 q hv
  | suzuki m => exact catalogueCase_suzuki m hv
  | reeG2 m => exact catalogueCase_reeG2 m hv
  | reeF4 m => exact ExcTw.catalogueCase_reeF4 m hv
  | tits => exact catalogueCase_tits hv

end

end CFSGOutside.HallPaige
