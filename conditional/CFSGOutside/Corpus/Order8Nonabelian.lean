import Mathlib

/-!
# Corpus input: nonabelian groups of order 8

Statement of `CFSG.OddStandard.SmallF3.HarrisU33.Outside.order8_nonabelian`
(`CFSG/LocalAnalysis/OddStandard/SmallF3/U33/Outside/OutOrder8.lean`, line 126, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim: a nonabelian group of order 8 is dihedral
of order 8 or quaternion.
-/

namespace CFSGOutside.Corpus

/-- A nonabelian group of order 8 is `D₄` or `Q₈`. -/
class Order8Nonabelian : Prop where
  order8_nonabelian : ∀ {G : Type} [Group G] [Finite G] (_h8 : Nat.card G = 8)
    (_hnab : ∃ a b : G, a * b ≠ b * a),
    Nonempty (G ≃* DihedralGroup 4) ∨ Nonempty (G ≃* QuaternionGroup 2)

end CFSGOutside.Corpus
