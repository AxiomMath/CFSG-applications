import CFSGOutside.HallPaige.Catalogue
import CFSGOutside.HallPaige.Alternating
import CFSGOutside.HallPaige.Cosets

/-!
# Catalogue cases proved without the classification-specific inputs
-/

namespace CFSGOutside.HallPaige

open TauCeti

/-- Every alternating group has a complete mapping (Hall–Paige 1955, Theorem 3). -/
theorem hasCompleteMapping_alternatingGroup (n : ℕ) :
    HasCompleteMapping (alternatingGroup (Fin n)) :=
  hasCompleteMapping_alternatingGroup_of_cosetStatement cosetStatement n

/-- The alternating entries of the list. -/
theorem catalogueCase_alternating (n : ℕ) (hn : 5 ≤ n) : CatalogueCase (.alternating n hn) :=
  fun _ _ => hasCompleteMapping_alternatingGroup n

end CFSGOutside.HallPaige
