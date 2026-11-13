import CFSGOutside.Gagola.Main
import CFSGOutside.Gagola.PerfectAux
import CFSGOutside.Gagola.NoOrderEight
import CFSGOutside.Gagola.Order8
import CFSGOutside.Gagola.PSL2Dihedral
import CFSGOutside.Gagola.Order16Rank2
import CFSGOutside.Gagola.Order16Rank3

/-!
# Gagola, Theorem 4.5, the perfect case

Let `(H, Z, χ)` be a fully ramified triple, `Z ≤ K ⊴ H` with `H/K` nonabelian simple, and suppose that every
nonabelian Sylow 2-subgroup of `H/Z` has order at most `16` (this is what the hypothesis of Theorem 4.5 gives).
Then we get a contradiction (`perfect_step`).

Let `P` be a Sylow 2-subgroup of `H/Z` and `S` its image in `H/K`, a Sylow 2-subgroup of `H/K`.

* If `S` is abelian, this is `not_simple_quotient` (Walter's theorem).
* Otherwise `P` is nonabelian, so `|S| ≤ |P| ≤ 16`, and `|S| ≥ 8`; so `|S| = 8` or `|S| = 16`.
* `|S| = 8`: `sylow8_false` (Brauer-Suzuki, Gorenstein-Walter and Gagola's Theorem 2.5).
* `|S| = 16`: then `|P| = 16`. By the classification of the groups of 2-rank at most 2 and by the
  Gorenstein-Harada order list, `S` contains an element of order `8` (or `H/K` has two primes with cyclic
  Sylow subgroups, against Theorem 2.5(a)); it comes from an element of order `8` in `P`, which is impossible
  in a group of type f.r. (`fr_no_order_eight`).
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus

noncomputable section

/-- A nonabelian simple group with a nonabelian Sylow 2-subgroup of order 16 contains an element of order 8
(or has two primes with nontrivial cyclic Sylow subgroups). -/
theorem sylow16_order_eight_or_two_primes [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}]
    [CardStatedClassicalModelTwo] [Gh74SectionalTwoRankFour]
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (S : Sylow 2 X) (hS : Nat.card S = 16) (hSnab : ¬ IsMulCommutative (S : Subgroup X)) :
    (∃ x ∈ (S : Subgroup X), orderOf x = 8) ∨ TwoCyclicPrimes X := by
  by_cases hrank : CFSGOutside.Corpus.Open.twoRank X ≤ 2
  · exact Or.inl (sylow16_rank_le_two hnonab S hS hSnab hrank)
  · exact Or.inr (sylow16_rank3 hnonab S hS (by omega))

section Main

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}

theorem not_twoCyclicPrimes (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K)
    [IsSimpleGroup (H ⧸ K)] : ¬ TwoCyclicPrimes (H ⧸ K) := by
  obtain ⟨-, hχ, θ, e, hθ, hres, he⟩ := hfr
  rintro ⟨p, r, hp, hr, hpr, h1, h2⟩
  obtain ⟨P1⟩ := (inferInstance : Nonempty (Sylow p (H ⧸ K)))
  obtain ⟨P2⟩ := (inferInstance : Nonempty (Sylow r (H ⧸ K)))
  obtain ⟨c1, n1⟩ := h1 P1
  obtain ⟨c2, n2⟩ := h2 P2
  exact thm_2_5_a hχ hθ hres he K hZK hpr P1 c1 n1 P2 c2 n2

/-- **Gagola, Theorem 4.5 (the step for a perfect group of type f.r.).** Let `(H, Z, χ)` be a fully ramified
triple, `Z ≤ K ⊴ H` with `H/K` nonabelian simple, and suppose that the nonabelian Sylow 2-subgroups of `H/Z`
have order at most `16`. This is impossible. -/
theorem perfect_step [WalterSplit] [CardOfReeTitsModelTwistedG2] [CardWalterJ1]
    [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    [RankTwoSylowShapes] [HoltAtMostOneInvolution.{0}] [CardStatedClassicalModelTwo]
    [Gh74SectionalTwoRankFour]
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    (hnonab : ∃ a b : H ⧸ K, a * b ≠ b * a)
    (h16 : ∀ P : Sylow 2 (H ⧸ Z), ¬ IsMulCommutative (P : Subgroup (H ⧸ Z)) → Nat.card P ≤ 16) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (H ⧸ Z)))
  set π := quotMap Z K hZK with hπ
  let S : Sylow 2 (H ⧸ K) := P.mapSurjective (quotMap_surjective Z K hZK)
  have hSeq : (S : Subgroup (H ⧸ K)) = (P : Subgroup (H ⧸ Z)).map π := Sylow.coe_mapSurjective _ _
  by_cases hS : IsMulCommutative (S : Subgroup (H ⧸ K))
  · exact not_simple_quotient hfr K hZK hnonab S hS
  have hPnab : ¬ IsMulCommutative (P : Subgroup (H ⧸ Z)) := fun hP =>
    hS (hSeq ▸ isMulCommutative_map π _)
  have hP16 : Nat.card P ≤ 16 := h16 P hPnab
  have hSP : Nat.card S ≤ Nat.card P := by
    have := Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective (P : Subgroup (H ⧸ Z)))
    have e : Nat.card S = Nat.card ((P : Subgroup (H ⧸ Z)).map π) := by rw [hSeq]
    rw [e]; exact this
  obtain ⟨n, hn3, hnS⟩ := sylow_two_nonabelian_card S hS
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have hn : n = 3 ∨ n = 4 := by omega
  rcases hn with rfl | rfl
  · exact sylow8_false hfr K hZK hnonab S (by rw [hnS]; norm_num) hS psl2OddSylow8
  · have hS16 : Nat.card S = 16 := by rw [hnS]; norm_num
    have hPcard : Nat.card P = 16 := by omega
    rcases sylow16_order_eight_or_two_primes hnonab S hS16 hS with ⟨x, hx, hx8⟩ | h2
    · rw [hSeq] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have h8 : 8 ∣ orderOf y := hx8 ▸ orderOf_map_dvd π y
      obtain ⟨z, hz, hz8⟩ := exists_orderOf_eight (P : Subgroup (H ⧸ Z)) hPcard hy h8
      exact fr_no_order_eight hfr P hPcard z hz hz8
    · exact not_twoCyclicPrimes hfr K hZK h2

end Main

end

end CFSGOutside.Gagola
