import CFSGOutside.Robinson.Definitions

/-!
# Robinson, Propositions 2.3 and 2.4, Corollary 2.5, Lemma 2.6

D. J. S. Robinson, *The structure of finite groups in which permutability is a transitive relation*, J. Austral.
Math. Soc. 70 (2001), 143–159, DOI 10.1017/S1446788700002573. Propositions 2.3 and 2.4, Corollary 2.5 and Lemma
2.6 for SC- and SNAC-groups, unconditionally. The definitions are in
`CFSGOutside.Robinson`; `coupling` maps to
`CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms.Outer`, a verbatim copy of the corpus definition
`CFSG.ComponentClassification.OuterAutomorphisms.Outer`.
-/

namespace CFSGOutsideClean.Robinson

open CFSGOutside.Robinson Subgroup QuotientGroup

theorem proposition_2_3 (G : Type) [Group G]
    [Finite G] :
    IsSNAC G ↔ ∃ (S D : Subgroup G) (_ : S.Normal) (_ : D.Normal), S ≤ D ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ D) ∧ IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' S)) := sorry

theorem proposition_2_4 (G : Type) [Group G]
    [Finite G] :
    IsSC G ↔ ∃ (D : Subgroup G) (_ : D.Normal), ⁅D, D⁆ = D ∧ IsSupersoluble (G ⧸ D) ∧
      IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' (centerIn D))) ∧
      IsSupersolublyEmbedded (centerIn D) := sorry

theorem corollary_2_5 (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsTGroup (derivedLimit G) ∧
      IsSupersoluble (G ⧸ derivedLimit G) := sorry

theorem lemma_2_6_i (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    centralizer (derivedLimit G : Set G) =
        (centralizer ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G))) :
          Set (G ⧸ centerIn (derivedLimit G)))).comap
          (QuotientGroup.mk' (centerIn (derivedLimit G))) ∧
      (centralizer (derivedLimit G : Set G)).Normal ∧
      Group.IsSolvable (centralizer (derivedLimit G : Set G)) ∧
      ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ centralizer (derivedLimit G : Set G) := sorry

theorem lemma_2_6_ii (G : Type) [Group G]
    [Finite G] (hG : IsSC G) (S : Subgroup G) (hSn : S.Normal) (hSs : Group.IsSolvable S)
    (hSmax : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ S) :
    (coupling (derivedLimit G)).ker =
      (derivedLimit G ⊔ S).map (QuotientGroup.mk' (derivedLimit G)) := sorry

theorem proposition_2_3_derivedLimit (G : Type)
    [Group G] [Finite G] (hG : IsSNAC G) :
    ∃ (S : Subgroup G) (_ : S.Normal), S ≤ derivedLimit G ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple ((derivedLimit G).map (QuotientGroup.mk' S)) := sorry

theorem proposition_2_4_derivedLimit (G : Type)
    [Group G] [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsSupersoluble (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple
        ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G)))) ∧
      IsSupersolublyEmbedded (centerIn (derivedLimit G)) := sorry

end CFSGOutsideClean.Robinson
