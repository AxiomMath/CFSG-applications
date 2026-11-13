import Mathlib

/-!
# Corpus input: Brauer-Suzuki, quaternion form

Statement of `CFSG.Quasithin.F6.false_of_sylow_quaternion`
(`CFSG/Quasithin/Background/F6CatRecogTools2.lean`, line 124, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim: no nonabelian simple group has a Sylow
2-subgroup isomorphic to `QuaternionGroup 2`.
-/

namespace CFSGOutside.Corpus

/-- No finite nonabelian simple group has a generalized quaternion Sylow 2-subgroup `Q₈`. -/
class BrauerSuzukiQuaternion : Prop where
  false_of_sylow_quaternion : ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (Q : Sylow 2 G)
    (_e : ↥(Q : Subgroup G) ≃* QuaternionGroup 2), False

end CFSGOutside.Corpus
