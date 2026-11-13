import CFSGOutside.Corpus.Defs.OddCoreDihedral

/-!
# Corpus input: a group with dihedral Sylow 2-subgroups, no normal 2-complement and trivial odd core

Statement of `CFSG.ABGDGroups.aSeven_or_exists_normal_psl2` (`CFSG/GroupTheory/ABGDGroups/LinearEmbedding.lean`,
line 43, at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962), copied verbatim (the corpus file
opens `CFSG.GorensteinWalter (PSL2 IsOddPrimePower HasDihedralSylowTwo ...)`, which here are the copies in
`CFSGOutside.Corpus.Defs.OddCoreDihedral`).
-/

namespace CFSGOutside.Corpus

open GorensteinWalter

/-- `aSeven_or_exists_normal_psl2`. -/
class ASevenOrExistsNormalPsl2 : Prop where
  aSeven_or_exists_normal_psl2 : ∀ {H : Type} [Group H] [Finite H]
    (_hDih : HasDihedralSylowTwo H)
    (_hNC : ¬ HasNormalPComplement 2 H) (_hO : oddCore H = ⊥),
    Nonempty (H ≃* alternatingGroup (Fin 7)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        ∃ N : Subgroup H, N.Normal ∧ Nonempty (N ≃* PSL2 F) ∧
          Subgroup.centralizer (N : Set H) = ⊥

end CFSGOutside.Corpus
