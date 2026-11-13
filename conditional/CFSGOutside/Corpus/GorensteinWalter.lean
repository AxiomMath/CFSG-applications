import Mathlib

/-!
# Corpus input: the Gorenstein–Walter theorem

Statement of `CFSG.GorensteinWalter.gorenstein_walter`, copied verbatim from `CFSG/Dihedral/GorensteinWalter.lean`
(line 14) at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. The corpus proof applies the
Gorenstein–Walter theorem vendored from Qiuzhen-CFSG (`CFSG/ThirdParty/QiuzhenCFSG/GorensteinWalter/`).

A nonabelian simple group with a dihedral Sylow `2`-subgroup is `A₇` or `PSL(2, q)`, `q ≥ 5` odd.
-/

open scoped MatrixGroups

namespace CFSGOutside.Corpus

/-- The Gorenstein–Walter theorem, as `CFSG.GorensteinWalter.gorenstein_walter` states it. -/
class GorensteinWalter : Prop where
  gorenstein_walter : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)),
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k))

end CFSGOutside.Corpus
