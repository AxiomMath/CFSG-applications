import Mathlib

/-!
# Corpus input: Gorenstein–Walter for simple groups

Statement of `CFSG.GorensteinWalter.gorenstein_walter`, copied verbatim from `CFSG/Dihedral/GorensteinWalter.lean`
(line 14) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. Its proof is a thin adapter over the vendored Qiuzhen-CFSG theorem.
-/

namespace CFSGOutside.Corpus

open scoped MatrixGroups

/-- A nonabelian simple group with dihedral Sylow 2-subgroups is `A₇` or `PSL(2, p^k)`, `p` odd, `p^k ≥ 5`. -/
class GorensteinWalterSimple : Prop where
  gorenstein_walter : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)),
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k))

end CFSGOutside.Corpus
