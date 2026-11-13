import Mathlib

/-!
# Copied corpus definitions: the Hopf cover and the Schur multiplier

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, file
`CFSG/RankThree/PerfectCover/HopfCover.lean` (lines 17–35), under `CFSGOutside.Corpus.RankThree.PerfectCover`:
`hopfEval`, `hopfRelations`, `hopfCommutatorRelations`, `HopfCover`, `hopfCommutatorRelations_le_relations`,
`hopfCoverMap` and `hopfMultiplier`. The proofs are the corpus ones.
-/

noncomputable section

namespace CFSGOutside.Corpus.RankThree.PerfectCover

open Subgroup

universe u

section Definitions

variable (S : Type u) [Group S]

/-- Copy of `CFSG.RankThree.PerfectCover.hopfEval`. -/
abbrev hopfEval : FreeGroup S →* S := FreeGroup.lift id

/-- Copy of `CFSG.RankThree.PerfectCover.hopfRelations`. -/
abbrev hopfRelations : Subgroup (FreeGroup S) := (hopfEval S).ker

/-- Copy of `CFSG.RankThree.PerfectCover.hopfCommutatorRelations`. -/
abbrev hopfCommutatorRelations : Subgroup (FreeGroup S) :=
  ⁅(⊤ : Subgroup (FreeGroup S)), hopfRelations S⁆

/-- Copy of `CFSG.RankThree.PerfectCover.HopfCover`. -/
abbrev HopfCover : Type u :=
  commutator (FreeGroup S) ⧸ (hopfCommutatorRelations S).subgroupOf (commutator (FreeGroup S))

theorem hopfCommutatorRelations_le_relations : hopfCommutatorRelations S ≤ hopfRelations S :=
  Subgroup.commutator_le_right _ _

/-- Copy of `CFSG.RankThree.PerfectCover.hopfCoverMap`. -/
def hopfCoverMap : HopfCover S →* S :=
  QuotientGroup.lift _ ((hopfEval S).comp (commutator (FreeGroup S)).subtype) fun _ hd =>
    hopfCommutatorRelations_le_relations S hd

/-- The Schur multiplier, as the kernel of the Hopf cover. Copy of `CFSG.RankThree.PerfectCover.hopfMultiplier`. -/
abbrev hopfMultiplier : Subgroup (HopfCover S) := (hopfCoverMap S).ker

end Definitions

end CFSGOutside.Corpus.RankThree.PerfectCover
