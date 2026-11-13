import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Copied corpus definition: membership in the simple-group catalogue

Verbatim copy, under `CFSGOutside.Corpus`, of `CFSG.Assembly.InCatalog` from `CFSG/Assembly/InCatalog.lean`
(line 10) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with `CFSG.Assembly.GroupProp`
(`CFSG/Assembly/Reduction.lean`, line 10) unfolded. The catalogue is TauCeti's `CFSGIndex`, the same index the
classification statement `TauCeti.ClassificationStatement` uses.
-/

namespace CFSGOutside.Corpus.Assembly

/-- `G` is isomorphic to a group in TauCeti's catalogue of finite simple groups. -/
def InCatalog (G : Type) [Group G] : Prop :=
  ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group)

end CFSGOutside.Corpus.Assembly
