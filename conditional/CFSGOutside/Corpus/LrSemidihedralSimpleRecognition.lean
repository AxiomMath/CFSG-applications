import CFSGOutside.Corpus.Defs.LowTwoRankCatalog

/-!
# Corpus input: simple groups with semidihedral Sylow 2-subgroups (Alperin–Brauer–Gorenstein)

Statement of `CFSG.Milestones.lr_semidihedral_simple_recognition_2`, copied verbatim from
`CFSG/Milestones/LR_semidihedral_simple_recognition.lean` (line 78) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `SemidihedralGroup`, `PSU3` and `M11` are the copies in
`CFSGOutside.Corpus.Defs`.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- Alperin–Brauer–Gorenstein, as `CFSG.Milestones.lr_semidihedral_simple_recognition_2` states it. -/
class LrSemidihedralSimpleRecognition : Prop where
  lr_semidihedral_simple_recognition_2 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (_hsd : ∃ n : ℕ, 4 ≤ n ∧ Nonempty ((P : Subgroup G) ≃* Open.SemidihedralGroup n)),
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 3 ∧
        Nonempty (G ≃* PSL(3, GaloisField p k))) ∨
    (∃ p k : ℕ, ∃ _hp : Fact p.Prime, 0 < k ∧ p ^ k % 4 = 1 ∧
        Nonempty (G ≃* Open.PSU3 p k)) ∨
    Nonempty (G ≃* Open.M11)

end CFSGOutside.Corpus
