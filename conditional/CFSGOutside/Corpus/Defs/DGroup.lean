import CFSGOutside.Corpus.PPrimeCore
import CFSGOutside.Corpus.Defs.OddCoreDihedral

/-!
# Copied corpus definitions: Bender's D-groups (Gorenstein–Walter)

Copied verbatim at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus.GorensteinWalter`, from
`CFSG/ThirdParty/QiuzhenCFSG/GorensteinWalter/Classification.lean` (lines 42–85), which is vendored from
Qiuzhen-CFSG. `pPrimeCore` is the copy `CFSGOutside.Corpus.pPrimeCore`; `HasDihedralSylowTwo`, `PSL2` and
`IsOddPrimePower` are the copies in `OddCoreDihedral.lean`.
-/

namespace CFSGOutside.Corpus.GorensteinWalter

open Matrix

universe u

/-- Sylow `2`-subgroups are cyclic or dihedral. Copy of `CFSG.GorensteinWalter.HasCyclicOrDihedralSylowTwo`,
line 48. -/
def HasCyclicOrDihedralSylowTwo (G : Type u) [Group G] : Prop :=
  ∀ S : Sylow 2 G,
    IsCyclic S ∨ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))

/-- `PGL(2,K)`. Copy of `CFSG.GorensteinWalter.PGL2`, line 57. -/
abbrev PGL2 (K : Type u) [CommRing K] :=
  ProjGenLinGroup (Fin 2) K

/-- Bender's D-groups. Copy of `CFSG.GorensteinWalter.IsDGroup`, line 70. -/
inductive IsDGroup (G : Type u) [Group G] [Finite G] : Prop
  | quotientIsTwoGroup
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (h : IsPGroup 2 (G ⧸ pPrimeCore 2 G))
  | quotientIsASeven
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (e : Nonempty ((G ⧸ pPrimeCore 2 G) ≃* alternatingGroup (Fin 7)))
  | quotientHasLinearNormalSubgroup
      (hSylow : HasCyclicOrDihedralSylowTwo G)
      (K : Type u) [Field K] [Finite K]
      (hKprimePower : IsOddPrimePower (Nat.card K))
      (L : Subgroup (G ⧸ pPrimeCore 2 G))
      (hLnormal : L.Normal)
      (hLindex : Odd L.index)
      (hLmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K))

end CFSGOutside.Corpus.GorensteinWalter
