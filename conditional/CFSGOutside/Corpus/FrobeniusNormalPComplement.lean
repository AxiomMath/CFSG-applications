import CFSGOutside.Corpus.Defs.FrobeniusFrattini

/-!
# Corpus input: Frobenius' normal `p`-complement theorem

Statement of `CFSG.GroupTheory.frobenius_normal_p_complement`, copied verbatim from
`CFSG/GroupTheory/FrobeniusNormalComplement.lean` (line 333) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `IsNormalPComplement` is the copy in
`CFSGOutside.Corpus.Defs.FrobeniusFrattini`. The corpus theorem is universe polymorphic; the class takes the universe
of `G` as a parameter.

`G` has a normal `p`-complement if and only if `N_G(Q)/C_G(Q)` is a `p`-group for every `p`-subgroup `Q`; a normal
`p`-complement is unique and characteristic.
-/

namespace CFSGOutside.Corpus

open Subgroup GroupTheory

/-- Frobenius' normal `p`-complement theorem, as `CFSG.GroupTheory.frobenius_normal_p_complement` states it. -/
class FrobeniusNormalPComplement.{u} : Prop where
  frobenius_normal_p_complement : ∀ {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime],
    ((∃ N : Subgroup G, IsNormalPComplement p N) ↔
      ∀ Q : Subgroup G, IsPGroup p Q → IsPGroup p (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G)))) ∧
    (∀ N₁ N₂ : Subgroup G, IsNormalPComplement p N₁ → IsNormalPComplement p N₂ → N₁ = N₂) ∧
    ∀ N : Subgroup G, IsNormalPComplement p N → N.Characteristic

end CFSGOutside.Corpus
