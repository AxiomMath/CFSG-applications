import Mathlib

/-!
# Copied corpus definition: the conjugate of a subgroup

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`. The clean build proves the copy equal to its original in
`clean/CFSGOutsideClean/Corpus/Defs/Conjugate.lean`.
-/

namespace CFSGOutside.Corpus

/-- The conjugate `g⁻¹ H g` of a subgroup. Copy of `CFSG.conjugate`, `CFSG/Foundations/Basic.lean` line 31. -/
def conjugate {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

end CFSGOutside.Corpus
