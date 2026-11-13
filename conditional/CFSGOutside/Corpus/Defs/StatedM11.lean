import CFSGOutside.Corpus.Defs.NativeM11

/-!
# Copied corpus definition: `StatedM11`

Copy of `CFSG.Open.StatedM11`, `CFSG/Open/StatedDefs.lean` line 91, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. In the corpus it is defined as `CFSG.Blueprint.NativeSporadic.M11`, whose copy
is in `CFSGOutside.Corpus.Defs.NativeM11`.
-/

namespace CFSGOutside.Corpus.Open

/-- The Mathieu group `M₁₁` as a permutation group. Copy of `CFSG.Open.StatedM11`. -/
def StatedM11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Blueprint.NativeSporadic.M11

end CFSGOutside.Corpus.Open
