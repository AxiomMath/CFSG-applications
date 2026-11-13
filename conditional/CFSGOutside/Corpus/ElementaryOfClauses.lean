import CFSGOutside.Corpus.Defs.J1Models

/-!
# Corpus input: Sylow 2-subgroups of the groups in Walter's list

Statement of `CFSG.Goldschmidt.GoldType.elementary_of_clauses`
(`CFSG/Goldschmidt/Steps/GoldType.lean`, line 116, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962), with the section variables `{K : Type} [Group K] [Finite K]`
(line 27) made explicit. `ordRee` and `goldschmidtJ1` are the copies in `CFSGOutside.Corpus.Defs`.
-/

open scoped MatrixGroups

namespace CFSGOutside.Corpus

/-- `PSL(2, q)` with `q ≡ ±3 mod 8`, simple groups of Ree order and `J₁` have elementary abelian Sylow
2-subgroups of order at least `4`, with transitive normalizer action. -/
class ElementaryOfClauses : Prop where
  elementary_of_clauses : ∀ {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (_hK : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (K ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card K = Open.ordRee (3 ^ (2 * m + 1))) ∨
        Nonempty (K ≃* Open.goldschmidtJ1))
    (T : Sylow 2 K),
    IsMulCommutative (T : Subgroup K) ∧ (∀ t ∈ (T : Subgroup K), t ^ 2 = 1) ∧
      4 ≤ Nat.card (T : Subgroup K) ∧
      ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), x ≠ 1 → y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n⁻¹ * x * n = y

end CFSGOutside.Corpus
