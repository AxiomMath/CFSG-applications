import Mathlib

/-!
# Corpus input: Sylow 2-subgroups of `SL(2,q)`, `q` odd, are generalized quaternion

Statement of `CFSG.ClassicalInvolution.specialLinearGroup_sylow_quaternion`, copied verbatim from
`CFSG/ClassicalInvolution/QuaternionStructure.lean` (line 105) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. The class takes the universe as a parameter.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- A Sylow 2-subgroup of `SL(2,F)`, `F` finite of odd characteristic, is generalized quaternion. -/
class SpecialLinearGroupSylowQuaternion.{u} : Prop where
  specialLinearGroup_sylow_quaternion : ∀ (F : Type u) [Field F] [Finite F]
    (_hF : ringChar F ≠ 2) (P : Sylow 2 SL(2, F)),
    ∃ k : ℕ, 1 ≤ k ∧ Nonempty ((P : Subgroup SL(2, F)) ≃* QuaternionGroup (2 ^ k))

end CFSGOutside.Corpus
