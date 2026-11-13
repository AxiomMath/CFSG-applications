import CFSGOutside.ChillagSonn.Lemma19C
import CFSGOutside.ChillagSonn.Theorem1Solvable

/-!
# Theorem 1 of Chillag–Sonn when `G/S(G)` is simple

`G = O(G) A` with `O(G) ∩ A = 1` and `A` a perfect stem extension of `G/S(G)` by a group of order at most 2
(`case1_split`). By Lemma (1.9), `A` centralizes `O(G)` unless `|Z(A)| = 2` and `|A/Z(A)| = 60`, that is
`A ≅ SL(2, 5)`. For a prime `q` dividing `|A|` and `|O(G)|` the Sylow statements follow from `sylow_claims`: with
`L = 1` when `A` centralizes `O(G)`, and in the exceptional case with `L` the normal Hall subgroup of `O(G)` for the
primes `≥ 7`, as `A` centralizes `O(G)/L` by Lemma (1.9) applied in `G/L` (the primes dividing `|O(G)/L|` are 3 and 5,
which divide `|SL(2, 5)| = 120`).
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.Open CFSGOutside.Corpus.RankThree.PerfectCover
  CFSGOutside.Corpus.GorensteinWalter
open scoped MatrixGroups

/-- An odd prime dividing 120 is 3 or 5. -/
theorem lt_seven_of_dvd_120 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : q ∣ 120) : q < 7 := by
  have h' : q ∣ 2 ^ 3 * (3 * 5) := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hq).mp h' with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)) hq2
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      omega

theorem dvd_120_of_lt_seven {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r < 7) : r ∣ 120 := by
  interval_cases r <;> first | exact absurd hr Nat.not_prime_zero | decide

variable [CardKerDvdHopfMultiplier] [PslTwoHopfMultiplier] [HopfMultiplierAlternating]
  [CardHopfMultiplierEqCardGriess] [FieldNineAlternatingSix.{0}] [HopfMultiplierM11]
  [MinimalNormalSimpleFactors.{0}] [TwoLePRankOfIsSimpleGroup.{0}] [LrRankTwoIsomorphismTypes]
  [CardStatedProjStatedSL] [CardPsuThreeMulGcd] [FrattiniElementaryQuotient.{0}]
  [FrattiniAutomorphismKernel.{0}] [HopfCentralCoverConsequences] [FrobeniusNormalPComplement.{0}]
  [DicksonPsl2SubgroupClassification.{0}]

/-- **Theorem 1, `G/S(G)` simple.** -/
theorem theorem_1_case1 {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G) (hns : ¬ Group.IsSolvable G)
    (hsimp : IsSimpleGroup (G ⧸ solvableRadical G)) : Theorem1Conclusion G := by
  classical
  have := hsimp
  obtain ⟨A, hinf, hsup, hPL, hqA, hZA, ⟨eA⟩⟩ := case1_split hG hns hsimp
  have hodd : Odd (Nat.card (oddCore G)) := odd_card_oddCore
  have hnab : ∃ a b : G ⧸ solvableRadical G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hqA.2.2
    exact ⟨eA a, eA b, fun h => hab (eA.injective (by simpa using h))⟩
  have hX : Lemma15Conclusion (G ⧸ solvableRadical G) := lemma_1_5 hnab (hG.quotient _)
  have hperf : commutator A = ⊤ := hqA.1.commutator_eq_top
  -- the exceptional case is `A ≅ SL(2, 5)`
  have hSL : Nat.card (Subgroup.center A) = 2 → Nat.card (A ⧸ Subgroup.center A) = 60 →
      Nonempty (A ≃* SL(2, ZMod 5)) := fun h2 h60 =>
    nonempty_sl_five_of_stem hperf (Subgroup.center A) le_rfl h2 eA hnab hX
      ((Nat.card_congr eA.toEquiv).symm.trans h60)
  have hcent : ¬ (Nat.card (Subgroup.center A) = 2 ∧ Nat.card (A ⧸ Subgroup.center A) = 60) →
      A ≤ Subgroup.centralizer (oddCore G : Set G) := fun hE =>
    le_centralizer_top hG A hqA hZA (oddCore G) hinf hodd (fun h2 h3 => absurd ⟨h2, h3⟩ hE)
  refine ⟨oddCore G, A, inferInstance, hinf, hsup, hodd, hasSylowTower_of_odd (hG.subgroup _) hodd,
    Or.inr ⟨rfl, ?_, Or.inl ⟨hPL, hperf, fun hE => hcent fun h => ?_⟩⟩⟩
  rotate_left
  · obtain ⟨e⟩ := hSL h.1 h.2
    exact hE.false e
  intro q hq hqA' hqN _
  have hq2 : q ≠ 2 := fun h => by
    rw [h] at hqN
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hqN)
  by_cases hE : Nat.card (Subgroup.center A) = 2 ∧ Nat.card (A ⧸ Subgroup.center A) = 60
  · -- `A ≅ SL(2, 5)`: work modulo the normal Hall subgroup `L` of `O(G)` for the primes `≥ 7`
    have hA120 : Nat.card A = 120 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center A), hE.1, hE.2]
    obtain ⟨H, hHc, hHcard⟩ :=
      exists_characteristic_upperPart (Nat.card (oddCore G)) rfl (hG.subgroup _) hodd 7
    have : (H.map (oddCore G).subtype).Normal := normal_map_subtype_of_characteristic H
    have hLcard : Nat.card (H.map (oddCore G).subtype) = upperPart 7 (Nat.card (oddCore G)) := by
      rw [Subgroup.card_map_of_injective (oddCore G).subtype_injective, hHcard]
    have hLN : H.map (oddCore G).subtype ≤ oddCore G := Subgroup.map_subtype_le H
    have hq7 : q < 7 := lt_seven_of_dvd_120 hq hq2 (hA120 ▸ hqA')
    refine sylow_claims hG (oddCore G) A hinf hsup hodd hqA' hqN (H.map (oddCore G).subtype)
      (hLcard ▸ not_dvd_upperPart_of_lt hq hq7) fun a ha _ x hx => ?_
    refine comm_mem_of_quotient hG A hqA hZA (oddCore G) (H.map (oddCore G).subtype) hLN hinf hodd
      (fun _ _ r hr hrN => ?_) a ha x hx
    have hmul := card_map_mk_mul hLN
    rw [hLcard, mul_comm] at hmul
    have hr7 := lt_of_dvd_of_upperPart Nat.card_pos.ne' hmul hr hrN
    have hr2 : r ≠ 2 := fun h => by
      have hNb : Odd (Nat.card ((oddCore G).map (QuotientGroup.mk' (H.map (oddCore G).subtype)))) :=
        Odd.of_dvd_nat hodd ⟨_, (card_map_mk_mul hLN).symm⟩
      rw [h] at hrN
      exact Nat.not_even_iff_odd.mpr hNb (even_iff_two_dvd.mpr hrN)
    rw [hA120]
    exact dvd_120_of_lt_seven hr hr2 hr7
  · -- `A` centralizes `O(G)`
    refine sylow_claims hG (oddCore G) A hinf hsup hodd hqA' hqN ⊥ (by rw [Subgroup.card_bot]; exact hq.not_dvd_one)
      fun a ha _ x hx => ?_
    have h := Subgroup.mem_centralizer_iff.mp (hcent hE ha) x hx
    rw [Subgroup.mem_bot]
    calc a * x * a⁻¹ * x⁻¹ = (x * a) * a⁻¹ * x⁻¹ := by rw [h]
      _ = 1 := by group

end CFSGOutside.ChillagSonn
