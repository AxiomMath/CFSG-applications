import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf
import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
import CFSG.Alternating.Multipliers.Small
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
import CFSG.RankThree.PerfectCover.HopfCentralCovers
import CFSGOutside.Corpus.SchurMultipliers
import CFSGOutsideClean.Corpus.Defs.GriessHopf
import CFSGOutsideClean.Corpus.Defs.HopfCover
import CFSGOutsideClean.Corpus.Defs.Components
import CFSGOutsideClean.Corpus.Defs.NativeM11

/-! The corpus proves the seven Schur-multiplier statements that `CFSGOutside.Corpus.SchurMultipliers` assumes. The
copied `griessHopfMultiplier`, `HopfCover`, `hopfMultiplier`, `IsQuasisimple` and `NativeSporadic.M11` are the corpus
definitions by `rfl`. `HopfMultiplierM11` writes the corpus `sporadicMultiplierOrder .M11` and
`NativeSporadic.Carrier .M11` by their values, so the corpus term checks against it definitionally. -/

universe u

namespace CFSGOutsideClean.Corpus

instance cardKerDvdHopfMultiplier : CFSGOutside.Corpus.CardKerDvdHopfMultiplier :=
  ⟨fun hP π hπ hcen => CFSG.EvenSporadicStandard.M24Std.card_ker_dvd_hopfMultiplier hP π hπ hcen⟩

instance pslTwoHopfMultiplier : CFSGOutside.Corpus.PslTwoHopfMultiplier :=
  ⟨fun hk hk9 => CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier hk hk9⟩

instance hopfMultiplierAlternating : CFSGOutside.Corpus.HopfMultiplierAlternating :=
  ⟨CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six,
    CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven⟩

instance cardHopfMultiplierEqCardGriess : CFSGOutside.Corpus.CardHopfMultiplierEqCardGriess :=
  ⟨fun S _ =>
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier S⟩

instance fieldNineAlternatingSix : CFSGOutside.Corpus.FieldNineAlternatingSix.{u} :=
  ⟨fun K _ _ hK =>
    CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism K hK⟩

instance hopfMultiplierM11 : CFSGOutside.Corpus.HopfMultiplierM11 :=
  ⟨CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M11⟩

instance hopfCentralCoverConsequences : CFSGOutside.Corpus.HopfCentralCoverConsequences :=
  ⟨fun X _ => CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X⟩

end CFSGOutsideClean.Corpus
