import CFSGOutside.GiuliettiKorchmaros.Thm61Central

/-!
# Giulietti–Korchmáros (2019), Theorem 6.1 for odd core-free groups

M. Giulietti, G. Korchmáros, *Algebraic curves with many automorphisms*, Adv. Math. 349 (2019), 162–211,
Theorem 6.1 (arXiv:1702.08812v2, `\label{structure}`), in the case `O(G) = 1` treated in §6.1, in group-theoretic form.

The printed theorem assumes that `G` is an automorphism group of a non-rational curve of even genus over an
algebraically closed field of odd characteristic. Its proof in §6.1 uses this only through Lemma 6.2: every
2-subgroup of `G` has a cyclic subgroup of index (at most) 2. Lemma 6.2 (the Hurwitz genus formula) is not formalized;
the theorem below assumes its conclusion, `CyclicIndexTwo G`.

The conclusion lists the paper's cases (i)–(xi) (see `Theorem61Conclusion`) and, as case (xii), `SL(2,3)`, which
satisfies all hypotheses but is missing from the printed list.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

/-- **Automorphism groups of curves.** Let G be a finite group with no nontrivial normal subgroup of odd order, in which
every 2-subgroup has a cyclic subgroup of index at most 2. Then G has odd order, or is a 2-group, or its derived
subgroup is SL(2, q) with q odd and q ≥ 5, or G embeds in PΓL(2, q) with q odd and q ≥ 3 and contains PSL(2, q), or
G has a normal subgroup PSL(3, q) with q ≡ 3 (mod 4), or PSU(3, q) with q ≡ 1 (mod 4), whose centralizer is trivial,
or G is isomorphic to A₇, M₁₁, GL(2, 3), the binary octahedral group or SL(2, 3), or G is a perfect group of order
5040 whose quotient by its centre is A₇.

Source: M. Giulietti and G. Korchmáros, Algebraic curves with many automorphisms, Adv. Math. 349 (2019), 162–211,
Theorem 6.1. https://doi.org/10.1016/j.aim.2019.04.003

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_6_1 [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [RankTwoSylowShapes]
    [UnitaryFourSylowStructure] [GorensteinWalterSimple] [LrSemidihedralSimpleRecognition]
    [SemilinearEquivAut.{0}] [AutAlternatingBijectiveConj] [M11AutInner] [NativeM11EquivOpen]
    [QuaternionSylowStructure.{0}] [SpecialLinearGroupSylowQuaternion.{0}] [ThompsonTransferLemma.{0}]
    (hP : CyclicIndexTwo G) (hO : OddCoreFree G) : Theorem61Conclusion G := by
  classical
  unfold Theorem61Conclusion
  rcases subsingleton_or_nontrivial G with hs | hnt
  · left
    rw [Nat.card_unique]
    exact odd_one
  obtain ⟨N, hN⟩ := exists_isMinimalNormal hnt
  by_cases hab : ∀ a b : N, a * b = b * a
  · obtain ⟨hcard, hexp⟩ := abelian_minimalNormal hP hO hN hab
    haveI := hN.1
    rcases hcard with h2 | h4
    · -- `|N| = 2`: a central involution
      have hNc : N ≤ Subgroup.center G := Complement.le_center_of_card_two h2
      obtain ⟨z, hzN, hz1⟩ : ∃ z ∈ N, z ≠ 1 := by
        by_contra h
        push Not at h
        have : N = ⊥ := eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (h x hx)
        rw [this, Subgroup.card_bot] at h2
        norm_num at h2
      have hz2 : orderOf z = 2 := orderOf_eq_prime (hexp z hzN) hz1
      rcases central_cases _ G rfl hP hO z (hNc hzN) hz2 with h | h | h | ⟨-, -, h | h⟩ | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · -- `|N| = 4`
      rcases four_cases hP hO hN h4 hexp with h | ⟨M, hMn, ⟨eM⟩, hC⟩
      · exact Or.inr (Or.inl h)
      · haveI := hMn
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ZMod 3, inferInstance, inferInstance, ringChar_zmod_three,
          by rw [card_zmod_three], embedding_PGammaL2 eM hC⟩)))
  · push Not at hab
    obtain ⟨a, b, hab⟩ := hab
    exact theorem61_of_nonabelian hP hO hN ⟨a, b, hab⟩

end CFSGOutside.GiuliettiKorchmaros
