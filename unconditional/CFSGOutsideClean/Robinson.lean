import Comparator.Solution
import CFSGOutside.Robinson.Paper
import CFSGOutsideClean.Corpus.Schreier

/-! Robinson, Propositions 2.3 and 2.4, Corollary 2.5 and Lemma 2.6, with the classification statement supplied by
the corpus, `CFSGComparator.classification`, and Schreier's conjecture for the catalogue supplied by the corpus. -/

namespace CFSGOutsideClean.Robinson

open CFSGOutside.Robinson Subgroup QuotientGroup

/-- **Groups with simple chief factors.** A finite group G has all its nonabelian chief factors simple if and only if it
has normal subgroups S ≤ D with S and G/D soluble and D/S a direct product of G-invariant simple groups. G has all
its chief factors simple if and only if some perfect normal subgroup D has G/D supersoluble, D/Z(D) a direct product
of G-invariant simple groups, and Z(D) supersolubly embedded in G. In both cases D can be taken to be the last term
G^(∞) of the derived series. If every chief factor of G is simple, then G^(∞) is a perfect group in which normality
is transitive, G/G^(∞) is supersoluble, the centralizer of G^(∞) is the soluble radical S of G, and the kernel of
the coupling G/G^(∞) → Out(G^(∞)) is G^(∞)S/G^(∞).

Source: D. J. S. Robinson, The structure of finite groups in which permutability is a transitive relation, J.
Austral. Math. Soc. 70 (2001), 143–159, Propositions 2.3 and 2.4, Corollary 2.5 and Lemma 2.6.
https://doi.org/10.1017/S1446788700002573 -/
theorem proposition_2_3 (G : Type) [Group G]
    [Finite G] :
    IsSNAC G ↔ ∃ (S D : Subgroup G) (_ : S.Normal) (_ : D.Normal), S ≤ D ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ D) ∧ IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' S)) :=
  CFSGOutside.Robinson.proposition_2_3 CFSGComparator.classification.{0} G

/-- **Robinson 2001, Proposition 2.4.** A finite group `G` is an SC-group if and only if there
is a perfect normal subgroup `D` such that `G/D` is supersoluble, `D/Z(D)` is a direct product of
`G`-invariant simple groups, and `Z(D)` is supersolubly embedded in `G`. -/
theorem proposition_2_4 (G : Type) [Group G]
    [Finite G] :
    IsSC G ↔ ∃ (D : Subgroup G) (_ : D.Normal), ⁅D, D⁆ = D ∧ IsSupersoluble (G ⧸ D) ∧
      IsDirectProductOfInvariantSimple (D.map (QuotientGroup.mk' (centerIn D))) ∧
      IsSupersolublyEmbedded (centerIn D) :=
  CFSGOutside.Robinson.proposition_2_4 CFSGComparator.classification.{0} G

/-- **Robinson 2001, Corollary 2.5.** An SC-group `G` is an extension of a perfect T-group by a
supersoluble group; namely `D = G^(∞)` is a perfect T-group and `G/D` is supersoluble. -/
theorem corollary_2_5 (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsTGroup (derivedLimit G) ∧
      IsSupersoluble (G ⧸ derivedLimit G) :=
  CFSGOutside.Robinson.corollary_2_5 CFSGComparator.classification.{0} G hG

/-- **Robinson 2001, Lemma 2.6(i).** Let `G` be an SC-group, `D = G^(∞)` and `R = D/Z(D)`. Then
`C_G(D) = C_G(R)`, and this is the soluble radical of `G` (a soluble normal subgroup containing
every soluble normal subgroup).  Here `C_G(R)` is the set of `g` acting trivially on `D/Z(D)`,
i.e. the preimage of the centralizer of `D/Z(D)` in `G/Z(D)`. -/
theorem lemma_2_6_i (G : Type) [Group G]
    [Finite G] (hG : IsSC G) :
    centralizer (derivedLimit G : Set G) =
        (centralizer ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G))) :
          Set (G ⧸ centerIn (derivedLimit G)))).comap
          (QuotientGroup.mk' (centerIn (derivedLimit G))) ∧
      (centralizer (derivedLimit G : Set G)).Normal ∧
      Group.IsSolvable (centralizer (derivedLimit G : Set G)) ∧
      ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ centralizer (derivedLimit G : Set G) :=
  CFSGOutside.Robinson.lemma_2_6_i CFSGComparator.classification.{0} G hG

/-- **Robinson 2001, Lemma 2.6(ii).** Let `G` be an SC-group, `D = G^(∞)` and `S` the soluble
radical of `G`. Then `DS/D` is the kernel of the coupling `χ : G/D → Out(D)`. -/
theorem lemma_2_6_ii (G : Type) [Group G]
    [Finite G] (hG : IsSC G) (S : Subgroup G) (hSn : S.Normal) (hSs : Group.IsSolvable S)
    (hSmax : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A ≤ S) :
    (coupling (derivedLimit G)).ker =
      (derivedLimit G ⊔ S).map (QuotientGroup.mk' (derivedLimit G)) :=
  CFSGOutside.Robinson.lemma_2_6_ii CFSGComparator.classification.{0} G hG S hSn hSs hSmax

/-- **Proposition 2.3, "⇒", with `D = G^(∞)`** (as in Robinson's proof). -/
theorem proposition_2_3_derivedLimit (G : Type)
    [Group G] [Finite G] (hG : IsSNAC G) :
    ∃ (S : Subgroup G) (_ : S.Normal), S ≤ derivedLimit G ∧ Group.IsSolvable S ∧
      Group.IsSolvable (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple ((derivedLimit G).map (QuotientGroup.mk' S)) :=
  CFSGOutside.Robinson.proposition_2_3_derivedLimit CFSGComparator.classification.{0} G hG

/-- **Proposition 2.4, "⇒", with `D = G^(∞)`** (as in Robinson's proof). -/
theorem proposition_2_4_derivedLimit (G : Type)
    [Group G] [Finite G] (hG : IsSC G) :
    ⁅derivedLimit G, derivedLimit G⁆ = derivedLimit G ∧ IsSupersoluble (G ⧸ derivedLimit G) ∧
      IsDirectProductOfInvariantSimple
        ((derivedLimit G).map (QuotientGroup.mk' (centerIn (derivedLimit G)))) ∧
      IsSupersolublyEmbedded (centerIn (derivedLimit G)) :=
  CFSGOutside.Robinson.proposition_2_4_derivedLimit CFSGComparator.classification.{0} G hG

end CFSGOutsideClean.Robinson
