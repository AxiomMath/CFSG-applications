import CFSGOutside.Corpus.Defs.SporadicOrder

/-!
# Corpus input: orders of the sporadic groups

Statement of `CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds`
(`CFSG/HardMathSupport/Solomon/Coordinator/SporOrders.lean`, line 12, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), which is `SporadicOrdersTable`
(`CFSG/HardMathSupport/Solomon/Coordinator/GFR2FamSpor.lean`, line 44) unfolded. `SporadicOrdersTable` is the
copy in `CFSGOutside.Corpus.Defs.SporadicOrder`.

The catalogue group of each of the 26 sporadic names has the order `sporOrd`.
-/

namespace CFSGOutside.Corpus

/-- The sporadic catalogue groups have the orders `sporOrd`, as `sporadicOrdersTable_holds` states it. -/
class SporadicOrdersTableHolds : Prop where
  sporadicOrdersTable_holds : HardMathSupport.Solomon.Coordinator.SporadicOrdersTable

end CFSGOutside.Corpus
