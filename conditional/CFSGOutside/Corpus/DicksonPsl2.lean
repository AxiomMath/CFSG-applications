import CFSGOutside.Corpus.Defs.ElementaryAbelian

/-!
# Corpus input: Dickson's classification of the subgroups of `PSL(2, q)`

Statement of `CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification`, copied verbatim from
the vendored Qiuzhen-CFSG file `CFSG/ThirdParty/QiuzhenCFSG/Glauberman/DicksonClassification.lean` (line 7086) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, with the abbreviation `PSL2MatrixGroup F =
Matrix.ProjectiveSpecialLinearGroup (Fin 2) F` (`CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/MatrixGroups/PSL2.lean`,
line 26) unfolded and `IsElementaryAbelian` the copy in `CFSGOutside.Corpus.Defs.ElementaryAbelian`. The theorem is
universe polymorphic; the class takes the universe of `F` as a parameter. This is vendored (public) code.
-/

namespace CFSGOutside.Corpus

/-- Dickson's theorem (Huppert II.8.27), as
`CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification` states it. -/
class DicksonPsl2SubgroupClassification.{u} : Prop where
  huppert_II_8_27_dickson_psl2_subgroup_classification : ∀ {F : Type u} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (_hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)),
    IsElementaryAbelian p H ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)))

end CFSGOutside.Corpus
