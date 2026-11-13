import CFSGOutside.Corpus.Defs.ClassicalModel
import CFSGOutside.Corpus.Defs.TwoRank
import CFSGOutside.Corpus.Defs.TwoGroupShapes

/-!
# Corpus input: Sylow 2-subgroups of simple groups of 2-rank two

Statement of `CFSG.RankTwoShapes.rank_two_sylow_shapes`
(`CFSG/LocalAnalysis/RankTwoShapes/SylowShapes.lean`, line 310, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). `CFSG.Assembly.twoRank` and
`CFSG.Assembly.LowTwoRank.StatedClassicalModel` are export aliases of the `CFSG.Open` definitions.
-/

namespace CFSGOutside.Corpus

/-- The Sylow 2-subgroup of a simple nonabelian group of 2-rank two is dihedral, semidihedral, wreathed, or
that of `PSU(3, 4)`. -/
class RankTwoSylowShapes : Prop where
  rank_two_sylow_shapes : ∀ {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (_hrank : Open.twoRank G = 2) (S : Sylow 2 G),
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* Open.SemidihedralGroup n)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup G) ≃* Open.WreathedTwoGroup n)) ∨
    (∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      Open.StatedClassicalModel H .PSU 3 2 2 ∧
        Nonempty ((S : Subgroup G) ≃* (U : Subgroup H)))

end CFSGOutside.Corpus
