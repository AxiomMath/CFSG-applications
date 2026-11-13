import CFSGOutside.Corpus.Defs.Walter

/-!
# Corpus input: Walter's theorem on simple groups with abelian Sylow `2`-subgroups

Statement of `CFSG.Walter.walter_structure` (`CFSG/Walter/Final.lean` line 19) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, with its hypothesis `hJ : JRStrongHyp` discharged by the corpus's own
proof `CFSG.Walter.jrStrongHyp_of_open (CFSG.Walter.W67.theorem_of_reeIdentNative (CFSG.Walter.W67.prop_6_6_of
W67.prop_4_1 W67.prop_5_6 (W67.lemma_6_2_of W67.prop_4_1 W67.prop_5_6) W67.lemma_6_5) (CFSG.Walter.Ree.reeIdentNative
CFSG.Walter.Ree.T2.baseExists)) CFSG.Walter.j1RecogHyp CFSG.Walter.jtThreeHyp` — the same proof the corpus uses for
`CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple`. The field is the conclusion of `walter_structure` copied
verbatim; `IsTypeL2`, `ReeTypeHyp` and `walterJ1` are the copies in `CFSGOutside.Corpus.Defs.Walter`.

A nonabelian simple group with an abelian Sylow `2`-subgroup is `PSL(2, q)` (`q = 2^f ≥ 4` or `q ≡ ±3 (mod 8)`), of
Ree type, or `J₁`.
-/

namespace CFSGOutside.Corpus

/-- Walter's theorem, as `CFSG.Walter.walter_structure` states it once `JRStrongHyp` is supplied. -/
class WalterStructure : Prop where
  walter_structure : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G) (_hP : IsMulCommutative (P : Subgroup G)),
    Walter.IsTypeL2 G ∨ Nonempty (Walter.Ward.ReeTypeHyp G) ∨ Nonempty (G ≃* Open.walterJ1)

end CFSGOutside.Corpus
