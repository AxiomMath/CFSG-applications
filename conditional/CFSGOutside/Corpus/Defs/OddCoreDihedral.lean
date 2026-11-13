import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Copied corpus definitions: odd core, dihedral Sylow 2-subgroups, PSL(2, q)

Copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, namespaces renamed
to live under `CFSGOutside.Corpus` (the copy of `CFSG.HasNormalPComplement` that this file used to repeat is
the one in `ElemThompson.lean`):

* `CFSG.oddCore` (`CFSG/GroupTheory/PCore/Defs.lean`, line 18),
* `CFSG.GorensteinWalter.HasDihedralSylowTwo`, `.IsOddPrimePower`, `.PSL2`
  (`CFSG/ThirdParty/QiuzhenCFSG/GorensteinWalter/Classification.lean`, lines 42-44, 62-63, 53-54),
* `CFSG.AGLEmbedding.PSL2GF` (`CFSG/LocalAnalysis/AGLEmbedding/LinTwoCatalog.lean`, line 10).
-/

namespace CFSGOutside.Corpus

section

variable (G : Type*) [Group G]

/-- Copy of `CFSG.oddCore`. -/
def oddCore : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}

/-- Copy of `CFSG.oddCore_normal`. -/
instance oddCore_normal : (oddCore G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

end

namespace GorensteinWalter

universe u

/-- Copy of `CFSG.GorensteinWalter.HasDihedralSylowTwo`. -/
def HasDihedralSylowTwo (G : Type u) [Group G] : Prop :=
  ∀ S : Sylow 2 G,
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m))

/-- `PSL(2,K)`. Copy of `CFSG.GorensteinWalter.PSL2`. -/
abbrev PSL2 (K : Type u) [CommRing K] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) K

/-- Copy of `CFSG.GorensteinWalter.IsOddPrimePower`. -/
def IsOddPrimePower (q : ℕ) : Prop :=
  ∃ p n : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ n ∧ q = p ^ n

end GorensteinWalter

namespace AGLEmbedding

/-- Copy of `CFSG.AGLEmbedding.PSL2GF`. -/
abbrev PSL2GF (p n : ℕ) [Fact p.Prime] : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p n)

end AGLEmbedding

end CFSGOutside.Corpus
