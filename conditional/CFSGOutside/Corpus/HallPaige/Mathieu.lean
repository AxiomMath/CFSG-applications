import Mathlib.GroupTheory.Perm.List
import Mathlib.Algebra.Group.Subgroup.Lattice
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Mathieu groups

The natural permutation models of the five Mathieu groups, copied verbatim from
`CFSG/Blueprint/NativeSporadic.lean` (AxiomMath/CFSG @ 69cb972), and the corpus theorems
identifying them with the TauCeti presented groups, stated as classes with their exact
signatures.
-/

namespace CFSGOutside.Corpus.Mathieu

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M11`, CFSG/Blueprint/NativeSporadic.lean:27. -/
def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]),
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M12`, CFSG/Blueprint/NativeSporadic.lean:31. -/
def M12 : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]),
    (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M22`, CFSG/Blueprint/NativeSporadic.lean:35. -/
def M22 : Subgroup (Equiv.Perm (Fin 22)) :=
  Subgroup.closure {(List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]),
    (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M23`, CFSG/Blueprint/NativeSporadic.lean:39. -/
def M23 : Subgroup (Equiv.Perm (Fin 23)) :=
  Subgroup.closure {(List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]),
    (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16])}

/-- Corpus: `CFSG.Blueprint.NativeSporadic.M24`, CFSG/Blueprint/NativeSporadic.lean:43. -/
def M24 : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure {(List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]),
    (List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22])}

/-- The corpus identification of the permutation models of the Mathieu groups with the presented groups. -/
class Bridges : Prop where
  /-- The permutation model of `M₁₁` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/M11.lean:236. -/
  m11_nonempty_mulEquiv : Nonempty (↥M11 ≃* TauCeti.SporadicName.M11.Group)
  /-- The permutation model of `M₁₂` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/M12.lean:365. -/
  m12_nonempty_mulEquiv : Nonempty (↥M12 ≃* TauCeti.SporadicName.M12.Group)
  /-- The permutation model of `M₂₂` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/M22.lean:623. -/
  m22_nonempty_mulEquiv : Nonempty (↥M22 ≃* TauCeti.SporadicName.M22.Group)
  /-- The permutation model of `M₂₃` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/M23Surj.lean:83. -/
  m23_nonempty_mulEquiv : Nonempty (↥M23 ≃* TauCeti.SporadicName.M23.Group)
  /-- The permutation model of `M₂₄` is isomorphic to the TauCeti presented group.
  Corpus: `CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv`, CFSG/Sporadic/Bridge/M24Surj.lean:74. -/
  m24_nonempty_mulEquiv : Nonempty (↥M24 ≃* TauCeti.SporadicName.M24.Group)

end CFSGOutside.Corpus.Mathieu
