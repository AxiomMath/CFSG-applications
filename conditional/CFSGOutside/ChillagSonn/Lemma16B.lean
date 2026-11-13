import CFSGOutside.ChillagSonn.Lemma16
import CFSGOutside.ChillagSonn.Lemma110

/-!
# Lemma (1.6), nonsimple case: `PSL(2, pⁿ)` has index 2 in `G/S(G)`

If `G/S(G)` is not simple, it is `PGL(2, pⁿ)` or `PGL*(2, p²)`, and its minimal normal subgroup `N ≅ PSL(2, pⁿ)` has
index 2.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter

/-- **Lemma (1.6)**, nonsimple case, with the simple subgroup of index 2. -/
theorem lemma_1_6_nonsimple [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}]
    [LrRankTwoIsomorphismTypes] [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [SemilinearEquivAut.{0}]
    [AutAlternatingBijectiveConj] [M11AutInner] {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G)
    (hns : ¬ Group.IsSolvable G) (hnot : ¬ IsSimpleGroup (G ⧸ solvableRadical G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (p n : ℕ), p.Prime ∧ (n = 1 ∨ n = 2) ∧ Nat.card F = p ^ n ∧
      5 ≤ p ^ n ∧ (Nonempty (G ⧸ solvableRadical G ≃* PGL2 F) ∨
        (n = 2 ∧ Nonempty (G ⧸ solvableRadical G ≃* PGLStar F))) ∧
      ∃ Y : Subgroup (G ⧸ solvableRadical G), Y.Normal ∧ Y.index = 2 ∧ IsSimpleGroup Y ∧
        (∃ a b : Y, a * b ≠ b * a) ∧ Nonempty (Y ≃* PSL2 F) := by
  set X := G ⧸ solvableRadical G
  have hX : SylowMetacyclic X := hG.quotient _
  have hrad : ∀ M : Subgroup X, M.Normal → Group.IsSolvable M → M = ⊥ :=
    fun M hM hs => eq_bot_of_normal_solvable_quotient M hM hs
  have hnt : (⊤ : Subgroup X) ≠ ⊥ := by
    intro h
    apply hns
    have hS : solvableRadical G = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have : (QuotientGroup.mk' (solvableRadical G) g) ∈ (⊥ : Subgroup X) := h ▸ Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff g).mp ((Subgroup.mem_bot).mp this)
    have : Group.IsSolvable (solvableRadical G) := isSolvable_solvableRadical
    exact Group.isSolvable_of_surjective (f := (solvableRadical G).subtype)
      (fun g => ⟨⟨g, hS ▸ Subgroup.mem_top g⟩, rfl⟩)
  obtain ⟨N, -, hNn, hN1, hmin⟩ := exists_minimalNormal_le (Subgroup.normal_top (G := X)) hnt
  have := hNn
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hN1 (hrad N hNn (Group.isSolvable_of_comm hcon))
  have := simple_main hX hNn hN1 hmin hnab
  have hC := centralizer_eq_bot hX hrad hnab
  have hNtop : N ≠ ⊤ := fun h => hnot
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)).isSimpleGroup
  rcases lemma_1_5 hnab (hX.subgroup N) with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨F, _, _, p, n, hp, hn, hF, h5, ⟨e⟩⟩
  · exact absurd (eq_top_of_alternatingSeven hX e hC) hNtop
  · exact absurd (eq_top_of_M11 e hC) hNtop
  · have hp2 : p ≠ 2 := by rintro rfl; rcases hn with rfl | rfl <;> norm_num at h5
    obtain ⟨φ, hφ, hR⟩ := embedding_PGammaL2 e hC
    have hE : ∀ E : Subgroup (PGammaL2 F), E ≤ φ.range → (∀ x ∈ E, x ^ 2 = 1) →
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 4 := by
      intro E hEle hsq _
      have h4 := hX.card_le_four (E.comap φ) fun x hx => by
        have := hsq _ hx
        rw [← map_pow] at this
        exact (map_eq_one_iff φ hφ).mp this
      have : Nat.card (E.comap φ) = Nat.card E := by
        rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hEle]
      omega
    have eR : X ≃* φ.range := MonoidHom.ofInjective hφ
    have hNcard : Nat.card N = Nat.card (PSL2 F) := Nat.card_congr e.toEquiv
    have hXcard : Nat.card X = Nat.card φ.range := Nat.card_congr eR.toEquiv
    have hchar := ringChar_ne_two_of_card hp hn hF h5
    have hidx : Nat.card X = 2 * Nat.card (PSL2 F) → N.index = 2 := fun h => by
      have := N.index_mul_card
      rw [hNcard, h] at this
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
    have hY : N.index = 2 → ∃ Y : Subgroup X, Y.Normal ∧ Y.index = 2 ∧ IsSimpleGroup Y ∧
        (∃ a b : Y, a * b ≠ b * a) ∧ Nonempty (Y ≃* PSL2 F) := fun h =>
      ⟨N, hNn, h, inferInstance, hnab, ⟨e⟩⟩
    rcases overgroups_of_noElemEight hp hp2 hn hF φ.range hR hE with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨hn2, hR', hcR⟩
    · exact absurd (Subgroup.eq_top_of_card_eq N (hNcard.trans
        (hXcard.trans (Nat.card_congr e'.toEquiv)).symm)) hNtop
    · refine ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5, Or.inl ⟨eR.trans e'⟩, hY (hidx ?_)⟩
      rw [hXcard, Nat.card_congr e'.toEquiv, LinearTwo.card_PGL2, ← LinearTwo.card_PSL2_mul_two F hchar,
        mul_comm]
    · exact ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5,
        Or.inr ⟨hn2, ⟨eR.trans (MulEquiv.subgroupCongr hR')⟩⟩, hY (hidx (hXcard.trans hcR))⟩

end CFSGOutside.ChillagSonn
