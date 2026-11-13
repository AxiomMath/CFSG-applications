import CFSGOutside.Corpus.SchurMultipliers
import CFSGOutside.ChillagSonn.LinearTwo
import CFSGOutside.ChillagSonn.Unipotent
import CFSGOutside.ChillagSonn.Defs

/-!
# Stem extensions of the simple groups of Lemma (1.5) by groups of order at most 2

The discussion before Theorem 1 of Chillag–Sonn (facts 1–3): a perfect group `A` with a central subgroup `D` of order
at most 2 such that `A/D` is `A₇`, `M₁₁` or `PSL(2, q)` is one of `A₇`, `Ã₇`, `M₁₁`, `PSL(2, q)`, `SL(2, q)`. The
Schur multiplier of `M₁₁` is trivial, and the quasisimple double cover of `PSL(2, q)` is unique (the Sylow
2-subgroup of its Schur multiplier has order 2), so it is `SL(2, q)`. These facts are corpus inputs.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter
open scoped MatrixGroups

/-- A field with at least 4 elements has `a ≠ 0` with `a ^ 2 ≠ 1`. -/
theorem exists_ne_zero_sq_ne_one (F : Type) [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have := h a ha
      have h' : (a - 1) * (a + 1) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h' with h1 | h1
      · simp [sub_eq_zero.1 h1]
      · simp [eq_neg_of_add_eq_zero_left h1]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

/-- `SL(2, F)` is perfect for `|F| ≥ 4`. -/
theorem commutator_sl2_eq_top (F : Type) [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    commutator SL(2, F) = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one F h4
  exact Matrix.SL2.commutator_eq_top ha hasq

/-- The kernel of a homomorphism `A → A/D → X`. -/
theorem ker_comp_mk {A X : Type} [Group A] [Group X] (D : Subgroup A) [D.Normal] (e : A ⧸ D ≃* X) :
    (e.toMonoidHom.comp (QuotientGroup.mk' D)).ker = D := by
  ext a
  simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

/-- The center of a central extension of a nonabelian simple group is the kernel. -/
theorem center_eq_of_simple_quotient {A X : Type} [Group A] [Group X] (D : Subgroup A) [D.Normal]
    (hD : D ≤ Subgroup.center A) (e : A ⧸ D ≃* X) [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center A = D := by
  refine le_antisymm (fun z hz => ?_) hD
  have hc : e (QuotientGroup.mk z) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hz y]
  have hbot : Subgroup.center X = ⊥ := by
    rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hc
  exact hc

/-- A perfect central extension of a nonabelian simple group is quasisimple. -/
theorem isQuasisimple_of_central {A X : Type} [Group A] [Group X] (hA : commutator A = ⊤) (D : Subgroup A)
    [D.Normal] (hD : D ≤ Subgroup.center A) (e : A ⧸ D ≃* X) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : IsQuasisimple A := by
  have hZ := center_eq_of_simple_quotient D hD e hnab
  let e' : A ⧸ Subgroup.center A ≃* X := (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  refine ⟨⟨hA⟩, e'.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (by simpa using congrArg e' h)⟩

/-- A finite field with `pⁿ ≥ 5` elements, `n ≤ 2`, has odd characteristic. -/
theorem ringChar_ne_two_of_card {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime) (hn : n = 1 ∨ n = 2)
    (hF : Nat.card F = p ^ n) (h5 : 5 ≤ p ^ n) : ringChar F ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have := charP_of_card_eq_pow (by rcases hn with rfl | rfl <;> norm_num) hF
  rw [ringChar.eq F p]
  rintro rfl
  rcases hn with rfl | rfl <;> norm_num at h5

/-- The Sylow 2-subgroups of a group of order `2m`, `m` odd, have order 2. -/
theorem card_sylow_two_of_card {M : Type} [Group M] (m : ℕ) (hm : Odd m) (hM : Nat.card M = 2 * m)
    (S : Sylow 2 M) : Nat.card S = 2 := by
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; have := hm.pos; omega)
  rw [Sylow.card_eq_multiplicity, hM, Nat.factorization_mul (by norm_num) (by have := hm.pos; omega),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])]
  norm_num

variable [PslTwoHopfMultiplier] [HopfMultiplierAlternating] [CardHopfMultiplierEqCardGriess]
  [FieldNineAlternatingSix.{0}] [HopfCentralCoverConsequences]

/-- A perfect central extension of `PSL(2, F)` by a group of order 2 is `SL(2, F)` (`|F| ≥ 5` odd). -/
theorem nonempty_mulEquiv_sl2 {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤) (D : Subgroup A)
    [D.Normal] (hD : D ≤ Subgroup.center A) (hD2 : Nat.card D = 2) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) (e : A ⧸ D ≃* PSL2 F) [IsSimpleGroup (PSL2 F)]
    (hnab : ∃ a b : PSL2 F, a * b ≠ b * a) : Nonempty (A ≃* SL(2, F)) := by
  classical
  have := Fintype.ofFinite F
  have hqA : IsQuasisimple A := isQuasisimple_of_central hA D hD e hnab
  have hZA : Nat.card (Subgroup.center A) = 2 := by rw [center_eq_of_simple_quotient D hD e hnab, hD2]
  have hqS : IsQuasisimple SL(2, F) :=
    isQuasisimple_of_central (commutator_sl2_eq_top F (by omega)) (Subgroup.center SL(2, F)) le_rfl
      (MulEquiv.refl _) hnab
  have hZS : Nat.card (Subgroup.center SL(2, F)) = 2 := LinearTwo.card_center_SL2 F hF
  have eA : A ⧸ Subgroup.center A ≃* PSL2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_of_simple_quotient D hD e hnab)).trans e
  have hcardF : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  have hodd : Odd (Nat.card F) := by
    obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
    rw [← hcardF, hcard]
    exact (hp.odd_of_ne_two hF).pow
  by_cases h9 : Nat.card F = 9
  · obtain ⟨ψ⟩ := FieldNineAlternatingSix.unique_field_nine_projective_linear_alternating_six_isomorphism F
      (by rw [hcardF, h9])
    have h6 : Nat.card (griessHopfMultiplier (alternatingGroup (Fin 6))) = 2 * 3 := by
      rw [← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
        HopfMultiplierAlternating.hopfMultiplier_alternatingGroup_six.2]
    exact (HopfCentralCoverConsequences.hopf_central_cover_consequences (alternatingGroup (Fin 6))).2
      (card_sylow_two_of_card 3 (by decide) h6) A SL(2, F) hqA hqS hZA hZS ⟨eA.trans ψ⟩ ⟨ψ⟩
  · obtain ⟨-, ⟨eM⟩⟩ := PslTwoHopfMultiplier.psl_two_hopfMultiplier (k := F) (by omega) (by omega)
    have hg : Nat.gcd 2 (Fintype.card F - 1) = 2 := by
      obtain ⟨k, hk⟩ := hodd
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    have h2 : Nat.card (griessHopfMultiplier PSL(2, F)) = 2 * 1 := by
      rw [Nat.card_congr eM.toEquiv, hg, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (HopfCentralCoverConsequences.hopf_central_cover_consequences PSL(2, F)).2
      (card_sylow_two_of_card 1 odd_one h2) A SL(2, F) hqA hqS hZA hZS ⟨eA⟩ ⟨MulEquiv.refl _⟩

variable [CardKerDvdHopfMultiplier] [HopfMultiplierM11]

/-- **Facts 1–3 of Chillag–Sonn.** A perfect group `A` with a central subgroup `D` of order at most 2 and `A/D`
isomorphic to a group of Lemma (1.5) is in the list `M₁₁, A₇, Ã₇, PSL(2, q), SL(2, q)`. -/
theorem perfectList_of_stem {A X : Type} [Group A] [Finite A] [Group X] (hA : commutator A = ⊤)
    (D : Subgroup A) [D.Normal] (hD : D ≤ Subgroup.center A) (hD2 : Nat.card D ≤ 2) (e : A ⧸ D ≃* X)
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hX : Lemma15Conclusion X) : PerfectList A := by
  have hD1 : 1 ≤ Nat.card D := Nat.card_pos
  rcases (show Nat.card D = 1 ∨ Nat.card D = 2 by omega) with h1 | h2
  · -- `D = 1`: `A ≅ X`
    have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D h1
    subst hbot
    let eA : A ≃* X := (QuotientGroup.quotientBot.symm).trans e
    rcases hX with ⟨⟨eX⟩⟩ | ⟨⟨eX⟩⟩ | ⟨F, _, _, p, n, hp, hn, hF, h5, ⟨eX⟩⟩
    · exact Or.inr (Or.inl ⟨eA.trans eX⟩)
    · exact Or.inl ⟨eA.trans eX⟩
    · exact Or.inr (Or.inr (Or.inr ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5,
        Or.inl ⟨eA.trans eX⟩⟩))
  · rcases hX with ⟨⟨eX⟩⟩ | ⟨⟨eX⟩⟩ | ⟨F, _, _, p, n, hp, hn, hF, h5, ⟨eX⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨D, inferInstance, le_inf hD (hA ▸ le_top), h2, ⟨e.trans eX⟩⟩))
    · -- `M₁₁` has trivial Schur multiplier
      exfalso
      let π : A →* Blueprint.NativeSporadic.M11 := ((e.trans eX).toMonoidHom).comp (QuotientGroup.mk' D)
      have hker : π.ker = D := ker_comp_mk D (e.trans eX)
      have hdvd := CardKerDvdHopfMultiplier.card_ker_dvd_hopfMultiplier hA π
        ((e.trans eX).surjective.comp (QuotientGroup.mk'_surjective D)) (hker ▸ hD)
      rw [hker, h2, ← CardHopfMultiplierEqCardGriess.card_hopfMultiplier_eq_card_griessHopfMultiplier,
        HopfMultiplierM11.nativeRow_M11] at hdvd
      omega
    · have : IsSimpleGroup (PSL2 F) := eX.symm.isSimpleGroup
      have hnab' : ∃ a b : PSL2 F, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnab
        exact ⟨eX a, eX b, fun h => hab (eX.injective (by simpa using h))⟩
      obtain ⟨eS⟩ := nonempty_mulEquiv_sl2 hA D hD h2 (ringChar_ne_two_of_card hp hn hF h5) (by omega)
        (e.trans eX) hnab'
      exact Or.inr (Or.inr (Or.inr ⟨F, inferInstance, inferInstance, p, n, hp, hn, hF, h5, Or.inr ⟨eS⟩⟩))

end CFSGOutside.ChillagSonn
