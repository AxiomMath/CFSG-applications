import CFSGOutside.HallPaige.Statements
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# The catalogue cases

`CatalogueCase i` is the minimal-counterexample step for the catalogue group `i.Group`: a good group all of
whose proper good subgroups have complete mappings itself has a complete mapping.
-/

namespace CFSGOutside.HallPaige

open TauCeti

/-- The minimal-counterexample step for one entry of the classification list. -/
def CatalogueCase (i : CFSGIndex) : Prop :=
  IsGood i.Group → ProperSubgroupsAdmissible i.Group → HasCompleteMapping i.Group

end CFSGOutside.HallPaige
