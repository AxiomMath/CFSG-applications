import CFSGOutside.Corpus.Defs.GriessHopf
import CFSGOutside.Corpus.Defs.HopfCover
import CFSGOutside.Corpus.Defs.Components
import CFSGOutside.Corpus.Defs.NativeM11

/-!
# Corpus inputs: Schur multipliers and covering groups

Statements copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962. The Schur
multiplier appears as `Open.griessHopfMultiplier` (Hopf's formula, copy in `CFSGOutside.Corpus.Defs.GriessHopf`) or as
`RankThree.PerfectCover.hopfMultiplier` (kernel of the Hopf cover, copy in `CFSGOutside.Corpus.Defs.HopfCover`);
`IsQuasisimple` is the copy in `CFSGOutside.Corpus.Defs.Components` and `NativeSporadic.M11` the copy in
`CFSGOutside.Corpus.Defs.NativeM11`.

* `CardKerDvdHopfMultiplier`: `CFSG.EvenSporadicStandard.M24Std.card_ker_dvd_hopfMultiplier`
  (`CFSG/LocalAnalysis/EvenSporadicStandard/M24Std/CResHopf.lean`, line 93).
* `PslTwoHopfMultiplier`: `CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier`
  (`CFSG/LieType/Steinberg/CentralExt/PSL2Multiplier.lean`, line 55).
* `HopfMultiplierAlternating`: `CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six` and
  `_seven` (`CFSG/Alternating/Multipliers/Small.lean`, lines 167 and 175).
* `CardHopfMultiplierEqCardGriess`:
  `CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier`
  (`.../Karpilovsky/Coordinator/ProvedRows.lean`, line 20).
* `FieldNineAlternatingSix`: `CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism`
  (`CFSG/LocalAnalysis/ComponentInitial/FieldNineAlternatingSix.lean`, line 11).
* `HopfMultiplierM11`: `CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M11`
  (`.../Karpilovsky/Coordinator/TrivialRows.lean`, line 130), with `NativeSporadic.Carrier .M11` unfolded to
  `NativeSporadic.M11` and `sporadicMultiplierOrder .M11` evaluated to `1`.
* `HopfCentralCoverConsequences`: `CFSG.RankThree.PerfectCover.hopf_central_cover_consequences`
  (`CFSG/RankThree/PerfectCover/HopfCentralCovers.lean`, line 16).
-/

namespace CFSGOutside.Corpus

open Open RankThree.PerfectCover
open scoped MatrixGroups

/-- The kernel of a perfect central extension divides the Schur multiplier. -/
class CardKerDvdHopfMultiplier : Prop where
  card_ker_dvd_hopfMultiplier : ∀ {P E : Type} [Group P] [Group E] (_hP : commutator P = ⊤) (π : P →* E)
    (_hπ : Function.Surjective π) (_hcen : π.ker ≤ Subgroup.center P),
    Nat.card π.ker ∣ Nat.card (griessHopfMultiplier E)

/-- The Schur multiplier of `PSL(2, k)`, `|k| ≥ 5`, `|k| ≠ 9`. -/
class PslTwoHopfMultiplier : Prop where
  psl_two_hopfMultiplier : ∀ {k : Type} [Field k] [Fintype k] (_hk : 5 ≤ Fintype.card k)
    (_hk9 : Fintype.card k ≠ 9),
    commutator PSL(2, k) = ⊤ ∧
      Nonempty (griessHopfMultiplier PSL(2, k) ≃* Multiplicative (ZMod (Nat.gcd 2 (Fintype.card k - 1))))

/-- The Schur multipliers of `A₆` and `A₇` are cyclic of order 6. -/
class HopfMultiplierAlternating : Prop where
  hopfMultiplier_alternatingGroup_six :
    IsCyclic (hopfMultiplier (alternatingGroup (Fin 6))) ∧
      Nat.card (hopfMultiplier (alternatingGroup (Fin 6))) = 6
  hopfMultiplier_alternatingGroup_seven :
    IsCyclic (hopfMultiplier (alternatingGroup (Fin 7))) ∧
      Nat.card (hopfMultiplier (alternatingGroup (Fin 7))) = 6

/-- The two descriptions of the Schur multiplier have the same order. -/
class CardHopfMultiplierEqCardGriess : Prop where
  card_hopfMultiplier_eq_card_griessHopfMultiplier : ∀ (S : Type) [Group S],
    Nat.card (hopfMultiplier S) = Nat.card (griessHopfMultiplier S)

/-- `PSL(2, 9) ≅ A₆`. -/
class FieldNineAlternatingSix.{u} : Prop where
  unique_field_nine_projective_linear_alternating_six_isomorphism : ∀ (K : Type u) [Field K] [Fintype K]
    (_hK : Fintype.card K = 9),
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 6))

/-- The Schur multiplier of `M₁₁` is trivial. -/
class HopfMultiplierM11 : Prop where
  nativeRow_M11 : Nat.card (hopfMultiplier ↥Blueprint.NativeSporadic.M11) = 1

/-- Quasisimple covers with center of 2-power order, from the Sylow 2-subgroup of the Schur multiplier. -/
class HopfCentralCoverConsequences : Prop where
  hopf_central_cover_consequences : ∀ (X : Type) [Group X],
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        ∀ S : Sylow 2 (Subgroup.center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'] [Finite L] [Finite L'],
        IsQuasisimple L → IsQuasisimple L' →
        Nat.card (Subgroup.center L) = 2 → Nat.card (Subgroup.center L') = 2 →
        Nonempty ((L ⧸ Subgroup.center L) ≃* X) →
        Nonempty ((L' ⧸ Subgroup.center L') ≃* X) → Nonempty (L ≃* L'))

end CFSGOutside.Corpus
