import CFSGOutside.Corpus.Defs.TwoRank
import CFSGOutside.Corpus.Defs.TwoGroupShapes

/-!
# Copied corpus definitions: PSU(3, q) and M₁₁

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that a build importing the corpus too sees no clash. The copies are:

* `Open.PSU3` and `Open.M11` from `CFSG/Open/Catalog.lean` (lines 15, 50).

`Open.twoRank`, `Open.SemidihedralGroup` and `Open.WreathedTwoGroup` are the copies in `TwoRank.lean` and
`TwoGroupShapes.lean`.
-/

namespace CFSGOutside.Corpus

namespace Open

open Matrix
open scoped MatrixGroups

/-- `PSU(3, p^k)` inside `PGL(3, p^(2k))`. Copy of `CFSG.Open.PSU3`, `CFSG/Open/Catalog.lean` line 15. -/
noncomputable def PSU3 (p k : ℕ) [Fact p.Prime] :
    Subgroup (ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) :=
  (Subgroup.closure {A : GL (Fin 3) (GaloisField p (2 * k)) |
      (Matrix.of fun i j =>
          (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) j i ^ (p ^ k)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    GeneralLinearGroup.det A = 1}).map ProjGenLinGroup.mk

/-- The Mathieu group `M₁₁`. Copy of `CFSG.Open.M11`, `CFSG/Open/Catalog.lean` line 50. -/
def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure
    {List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
      List.formPerm [2, 6, 10, 7] * List.formPerm [3, 9, 4, 5]}

end Open

end CFSGOutside.Corpus
