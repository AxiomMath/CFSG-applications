import Mathlib

/-!
# Corpus input: Yoshida's transfer theorem

Statement of `CFSG.RankThree.Transfer.inf_commutator_eq_inf_map_commutator_normalizer`
(`CFSG/RankThree/Transfer/Control.lean`, line 78, at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962). In the corpus, `N` is local notation for
`Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G)`; it is written out here.

The corpus theorem is universe polymorphic, so the class takes the universe as a parameter.
-/

universe u

namespace CFSGOutside.Corpus

/-- **Yoshida**: if no quotient of the Sylow `p`-subgroup `P` is isomorphic to `C_p ≀ C_p`, then
`P ∩ G' = P ∩ N_G(P)'`. -/
class YoshidaTransfer : Prop where
  inf_commutator_eq_inf_map_commutator_normalizer : ∀ {G : Type u} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G)
    (_hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))),
    (P : Subgroup G) ⊓ commutator G =
      (P : Subgroup G) ⊓ (commutator (Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G))).map
        (Subgroup.subtype (Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G)))

end CFSGOutside.Corpus
