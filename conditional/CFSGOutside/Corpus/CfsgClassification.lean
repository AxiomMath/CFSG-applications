import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Corpus input: the classification of finite simple groups

Statement of `CFSG.Milestones.cfsg_classification`, copied verbatim from `CFSG/Milestones/CFSG_classification.lean`
(line 4575) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. It is the unfolding of
`TauCeti.ClassificationStatement.{0}` (`TauCeti.classificationStatement_iff`). The clean build provides the
instance, in `clean/CFSGOutsideClean/Corpus/CfsgClassification.lean`, from `CFSGComparator.classification`.
-/

namespace CFSGOutside.Corpus

/-- Every finite simple group is isomorphic to a group of TauCeti's catalogue. -/
class CfsgClassification : Prop where
  cfsg_classification : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group)

end CFSGOutside.Corpus
