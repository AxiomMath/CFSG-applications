import CFSGOutside.Corpus.Defs.ElemThompson

/-!
# Corpus input: Thompson's normal `p`-complement theorem

Statement of `CFSG.RankThree.Coprime.thompson_elementary_normal_p_complement`, copied verbatim from
`CFSG/RankThree/Coprime/ThompsonElementaryComplement.lean` (line 1057) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. For `p` odd and `P ∈ Syl_p(G)`: if `C_G(Z(P))` and `N_G(J_e(P))` have
normal `p`-complements, so does `G`. The copied definitions it mentions (`HasNormalPComplement`, `elemThompson`)
live in `CFSGOutside.Corpus.Defs.ElemThompson`.

The corpus theorem is universe polymorphic, so the class takes the universe as a parameter. The clean build
provides every instance, in `clean/CFSGOutsideClean/Corpus/ThompsonElementaryNormalPComplement.lean`.
-/

universe u

namespace CFSGOutside.Corpus

open Subgroup

/-- Thompson's normal `p`-complement theorem, as `thompson_elementary_normal_p_complement` states it. -/
class ThompsonElementaryNormalPComplement : Prop where
  thompson_elementary_normal_p_complement : ∀ {G : Type u} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (_hp2 : p ≠ 2) (P : Sylow p G)
    (_hC : HasNormalPComplement p ↥(centralizer
      (((center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) : Set G)))
    (_hN : HasNormalPComplement p ↥(normalizer
      (((elemThompson (P : Subgroup G) p).map (P : Subgroup G).subtype : Subgroup G) : Set G))),
    HasNormalPComplement p G

end CFSGOutside.Corpus
