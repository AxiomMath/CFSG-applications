import Mathlib

/-!
# Copied corpus definition: the native model of `M₁₁`

Copy of `CFSG.Blueprint.NativeSporadic.M11`, `CFSG/Blueprint/NativeSporadic.lean` line 27, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962.
-/

namespace CFSGOutside.Corpus.Blueprint.NativeSporadic

/-- The Mathieu group `M₁₁` as a permutation group (native generators). -/
def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure {(List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]),
    (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8])}

end CFSGOutside.Corpus.Blueprint.NativeSporadic
