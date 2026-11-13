import CFSGOutside.Corpus.LrRankTwoIsomorphismTypes
import CFSGOutside.Corpus.CardStatedProjStatedSL
import CFSGOutside.Corpus.CardPsuThreeMulGcd
import CFSGOutside.Corpus.TwoLePRankOfIsSimpleGroup
import CFSGOutside.ChillagSonn.Metacyclic
import CFSGOutside.ChillagSonn.Unipotent

/-!
# Lemma (1.5): the nonabelian simple Sylow-metacyclic groups

A nonabelian finite simple Sylow-metacyclic group is `A₇`, `M₁₁` or `PSL(2, pⁿ)` with `n ≤ 2` and `pⁿ ≥ 5`.

As in the paper: its 2-rank is 2 (at least 2 for every nonabelian simple group, at most 2 because a metacyclic
2-group has no elementary abelian subgroup of order 8), so the Alperin–Brauer–Gorenstein classification of the simple
groups of 2-rank two applies. `PSL(3, q)`, `PSU(3, q)` (`q` odd), `PSU(3, 4)` and `PSL(2, pⁿ)` with `n ≥ 3` are
excluded because their Sylow `p`-subgroups (`p` the characteristic) have small exponent (`p`, resp. 4) but order at
least `p³`, resp. `2⁶`, while a metacyclic group of exponent `e` has order dividing `e²`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.GorensteinWalter

/-- In a Sylow-metacyclic group, if `pᵏ` divides the order and all `p`-subgroups have exponent dividing `pᵇ`, then
`k ≤ 2b`. -/
theorem le_of_pow_dvd_card {M : Type} [Group M] [Finite M] (hM : SylowMetacyclic M) {p : ℕ} [hp : Fact p.Prime]
    {k b : ℕ} (hk : p ^ k ∣ Nat.card M) (he : ∀ Q : Subgroup M, IsPGroup p Q → ∀ x ∈ Q, x ^ (p ^ b) = 1) :
    k ≤ 2 * b := by
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hk
  have hQp : IsPGroup p Q := IsPGroup.of_card hQ
  have h := hM.card_dvd_sq Q hQp (he Q hQp)
  rw [hQ, ← pow_mul, mul_comm] at h
  exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h

/-- The exponent bound of `Unipotent.lean`, transported along an isomorphism with a model. -/
theorem le_of_model {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} {H : Subgroup (GL (Fin n) K)} (e : G ≃* StatedProj H) {k b : ℕ}
    (hk : p ^ k ∣ Nat.card G) (hb : n ≤ p ^ b) : k ≤ 2 * b := by
  have : Finite (StatedProj H) := Finite.of_equiv G e.toEquiv
  refine le_of_pow_dvd_card (hG.of_mulEquiv e) (by rwa [← Nat.card_congr e.toEquiv]) ?_
  intro Q hQ x hx
  exact statedProj_pow_eq_one_of_isPGroup H Q hQ hb x hx

theorem not_two_dvd_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ) : ¬ 2 ∣ p ^ f := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)
  exact hp2 this.symm

/-- A nonabelian simple Sylow-metacyclic group has 2-rank 2. -/
theorem twoRank_eq_two [TwoLePRankOfIsSimpleGroup.{0}] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hab : ∃ a b : G, a * b ≠ b * a) (hG : SylowMetacyclic G) : twoRank G = 2 := by
  unfold twoRank Open.pRank
  have hbdd : BddAbove {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card G, fun r ⟨A, _, _, hA⟩ => ?_⟩
    have := Subgroup.card_le_card_group A
    have h3 : r < 2 ^ r := Nat.lt_two_pow_self
    omega
  apply le_antisymm
  · apply csSup_le'
    rintro k ⟨E, -, ⟨-, hs⟩, hk⟩
    have h4 := hG.card_le_four E hs
    rw [hk] at h4
    by_contra hlt
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 3 ≤ k by omega)
    omega
  · have h2 := TwoLePRankOfIsSimpleGroup.two_le_pRank_of_isSimpleGroup hab
    unfold CFSGOutside.Corpus.pRank at h2
    have hne : {r : ℕ | ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h] at h2
      simp at h2
    have hbdd' : BddAbove {r : ℕ | ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
      refine ⟨Nat.card G, fun r ⟨A, _, hA⟩ => ?_⟩
      have := Subgroup.card_le_card_group A
      have h3 : r < 2 ^ r := Nat.lt_two_pow_self
      omega
    obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd'
    refine le_trans h2 (le_csSup hbdd ⟨A, le_top, ⟨hA.toIsMulCommutative, fun x hx => ?_⟩, hcard⟩)
    obtain ⟨k, hk⟩ := hA.exponent_dvd_p
    have := congrArg Subtype.val
      (show (⟨x, hx⟩ : A) ^ 2 = 1 by rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow])
    simpa using this

theorem pow_dvd_of_mul_eq {m g A p k : ℕ} (hm : m * g = A) (hA : p ^ k ∣ A) (hc : Nat.Coprime (p ^ k) g) :
    p ^ k ∣ m :=
  hc.dvd_of_dvd_mul_right (hm ▸ hA)

theorem coprime_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (k : ℕ) : Nat.Coprime (p ^ k) (p ^ f - 1) := by
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem coprime_pow_add_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (k : ℕ) : Nat.Coprime (p ^ k) (p ^ f + 1) := by
  refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have : p ∣ 1 := (Nat.dvd_add_right h1).mp h
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 2

/-- **Chillag–Sonn, Lemma (1.5).** A nonabelian finite simple Sylow-metacyclic group is isomorphic to `A₇`, `M₁₁` or
`PSL(2, pⁿ)` with `n ≤ 2` and `pⁿ ≥ 5`. -/
theorem lemma_1_5 [LrRankTwoIsomorphismTypes] [TwoLePRankOfIsSimpleGroup.{0}] [CardStatedProjStatedSL]
    [CardPsuThreeMulGcd] {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hab : ∃ a b : G, a * b ≠ b * a)
    (hG : SylowMetacyclic G) : Lemma15Conclusion G := by
  have hrank := twoRank_eq_two hab hG
  rcases LrRankTwoIsomorphismTypes.lr_rank_two_isomorphism_types G hab hrank with
    ⟨p, f, hp, hp2, hf, hadm, K, _, _, hK, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, K, _, _, hK, ⟨e⟩⟩ |
    ⟨p, f, hp, hp2, hf, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩ | h | h
  · -- `PSL(2, pᶠ)`: `f ≤ 2`
    have : Fact p.Prime := ⟨hp⟩
    have := charP_of_card_eq_pow hf hK
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hcard := CardStatedProjStatedSL.card_statedProj_statedSL (K := K) (n := 2) (by norm_num)
    rw [show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton, hK] at hcard
    norm_num at hcard
    have hg : Nat.gcd 2 (p ^ f - 1) ∣ p ^ f * ((p ^ f) ^ 2 - 1) :=
      dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one _)) _
    have hq : p ^ f ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, hcard]
      exact pow_dvd_of_mul_eq (Nat.div_mul_cancel hg) (dvd_mul_right _ _)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (coprime_pow_sub_one hp hf f))
    have hf2 : f ≤ 2 := by
      have := le_of_model hG e hq (b := 1) (by rw [pow_one]; omega)
      omega
    right; right
    refine ⟨K, inferInstance, inferInstance, p, f, hp, by omega, hK, ?_, ⟨e.trans
      (projectiveSpecialLinearEquivStatedProj 2 K).symm⟩⟩
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    have hodd : ¬ 2 ∣ p ^ f := not_two_dvd_of_odd_prime hp hp2 f
    have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    by_contra hlt
    push Not at hlt
    interval_cases h : p ^ f
    · exact h22 rfl
    · exact h23 rfl
    · exact hodd ⟨2, rfl⟩
  · -- `PSL(3, pᶠ)` is not Sylow-metacyclic
    exfalso
    have : Fact p.Prime := ⟨hp⟩
    have := charP_of_card_eq_pow hf hK
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hcard := CardStatedProjStatedSL.card_statedProj_statedSL (K := K) (n := 3) (by norm_num)
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num), hK] at hcard
    norm_num at hcard
    have hg : Nat.gcd 3 (p ^ f - 1) ∣ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
        ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one _)) _) _
    have hq : p ^ 3 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv, hcard]
      refine pow_dvd_of_mul_eq (Nat.div_mul_cancel hg) (dvd_mul_of_dvd_left ?_ _)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (coprime_pow_sub_one hp hf 3))
      exact pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3
    have := le_of_model hG e hq (b := 1) (by rw [pow_one]; omega)
    omega
  · -- `PSU(3, pᶠ)` is not Sylow-metacyclic
    exfalso
    have : Fact p.Prime := ⟨hp⟩
    have := charP_of_card_eq_pow (f := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hcard := CardPsuThreeMulGcd.card_psu_three_mul_gcd hp hf hK
    have hq : p ^ 3 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      refine pow_dvd_of_mul_eq hcard (dvd_mul_of_dvd_left ?_ _)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) (coprime_pow_add_one hp hf 3))
      exact pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 3
    have := le_of_model hG e hq (b := 1) (by rw [pow_one]; omega)
    omega
  · -- `PSU(3, 4)` is not Sylow-metacyclic
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := charP_of_card_eq_pow (p := 2) (f := 4) (by norm_num) (by rw [hK]; norm_num)
    have hcard := CardPsuThreeMulGcd.card_psu_three_mul_gcd (K := K) Nat.prime_two (f := 2) (by norm_num) hK
    have hq : 2 ^ 6 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      refine pow_dvd_of_mul_eq hcard (dvd_mul_of_dvd_left (by norm_num) _) (by norm_num)
    have := le_of_model hG e hq (b := 2) (by norm_num)
    omega
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSGOutside.ChillagSonn
