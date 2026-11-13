import Mathlib

/-!
# Corpus input: 5-transitive permutation groups of degree at most 80

Statement of `CFSG.FiveTransitive.subgroup_card_classification_of_card_le_eighty`, copied verbatim from
`CFSG/Permutation/FiveTransitive.lean` (line 35) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. The clean build provides the instance from the corpus theorem, in
`clean/CFSGOutsideClean/Corpus/SubgroupCardClassificationOfCardLeEighty.lean`.
-/

namespace CFSGOutside.Corpus

/-- A 5-transitive permutation group of degree `5 ≤ n ≤ 80` is `S_n`, `A_n`, `M₁₂` or `M₂₄`, by order. -/
class SubgroupCardClassificationOfCardLeEighty : Prop where
  subgroup_card_classification_of_card_le_eighty :
    ∀ n : ℕ, ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (P : Subgroup (Equiv.Perm Y)),
      Fintype.card Y = n → 5 ≤ n → n ≤ 80 → MulAction.IsMultiplyPretransitive P Y 5 →
      Nat.card P = n.factorial ∨
        (7 ≤ n ∧ Nat.card P = n.factorial / 2) ∨
        (n = 12 ∧ Nat.card P = 95040) ∨
        (n = 24 ∧ Nat.card P = 244823040)

end CFSGOutside.Corpus
