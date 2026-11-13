import CFSGOutside.ChillagSonn.Defs
import CFSGOutside.ChillagSonn.PNilpotent

/-!
# Odd-order Sylow-metacyclic groups have a Sylow tower

Gorenstein, *Finite Groups*, p. 259, as cited by Chillag–Sonn: peel off normal `p`-complements for the smallest
prime `p`, which exist by `exists_normalPComplement_of_metacyclic` because no larger odd prime divides `p ± 1`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GroupTheory

/-- If every prime factor of `n ≠ 0` is `≥ t`, then `upperPart t n = n`. -/
theorem upperPart_eq_self {t n : ℕ} (hn : n ≠ 0) (h : ∀ q ∈ n.primeFactors, t ≤ q) : upperPart t n = n := by
  rw [upperPart, Finset.filter_true_of_mem h, ← Nat.prod_primeFactors_pow_factorization hn]

/-- Multiplying by a power of a prime `p < t` does not change `upperPart t`. -/
theorem upperPart_mul_pow {t p m k : ℕ} (hp : p.Prime) (hpt : p < t) (hm : m ≠ 0) :
    upperPart t (m * p ^ k) = upperPart t m := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hne : ∀ q, t ≤ q → q ≠ p := fun q hq h => by omega
  have hS : (m * p ^ k).primeFactors.filter (t ≤ ·) = m.primeFactors.filter (t ≤ ·) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primeFactors, ne_eq, mul_eq_zero, hm, hpk, or_self,
      not_false_eq_true, and_true]
    refine ⟨fun ⟨⟨hq, hd⟩, htq⟩ => ⟨⟨hq, ?_⟩, htq⟩, fun ⟨⟨hq, hd⟩, htq⟩ => ⟨⟨hq, hd.mul_right _⟩, htq⟩⟩
    rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)) (hne q htq)
  rw [upperPart, upperPart, hS]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hqp := hne q (Finset.mem_filter.1 hq).2
  simp [Nat.factorization_mul hm hpk, hp.factorization, Finsupp.single_apply, Ne.symm hqp]

/-- Strengthened Sylow tower statement, with characteristic subgroups, by induction on the order. -/
theorem exists_characteristic_upperPart [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] (n : ℕ) :
    ∀ {N : Type} [Group N] [Finite N], Nat.card N = n → SylowMetacyclic N → Odd n →
      ∀ t, ∃ H : Subgroup N, H.Characteristic ∧ Nat.card H = upperPart t n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N _ _ hcard hN hodd t
  by_cases h1 : n = 1
  · subst h1; exact ⟨⊥, inferInstance, by simp [upperPart]⟩
  have hn0 : n ≠ 0 := hodd.pos.ne'
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpodd : Odd p := hp.odd_of_ne_two fun h => by
    rw [h] at hpn; exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨j, hj⟩ := hpodd; omega
  have hr : ∀ r : ℕ, r.Prime → r ∣ Nat.card N → r ≠ p → ¬ r ∣ p - 1 ∧ ¬ r ∣ p + 1 := by
    intro r hr hrN hrp
    rw [hcard] at hrN
    have hpr : p ≤ r := Nat.minFac_le_of_dvd hr.two_le hrN
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb⟩ := Odd.of_dvd_nat hodd hrN
    have : p + 1 < r := by omega
    exact ⟨Nat.not_dvd_of_pos_of_lt (by omega) (by omega), Nat.not_dvd_of_pos_of_lt (by omega) this⟩
  obtain ⟨K, hK⟩ := exists_normalPComplement_of_metacyclic (G := N) (p := p) (fun P => hN p P) hr
  have hKc : K.Characteristic :=
    (FrobeniusNormalPComplement.frobenius_normal_p_complement (G := N) p).2.2 K hK
  obtain ⟨_, hKcop, k, hk⟩ := hK
  have hpK : ¬ p ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd hp).1 hKcop.symm
  have hnK : n = Nat.card K * p ^ k := by rw [← hk, Subgroup.card_mul_index, hcard]
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [pow_zero, mul_one] at hnK; exact hpK (by rw [← hnK]; exact hpn)
  have hlt : Nat.card K < n := by
    rw [hnK]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hK0) (Nat.one_lt_pow hk0 hp.one_lt)
  have hoddK : Odd (Nat.card K) := Odd.of_dvd_nat hodd (hnK ▸ dvd_mul_right _ _)
  by_cases htp : t ≤ p
  · refine ⟨⊤, inferInstance, ?_⟩
    rw [Subgroup.card_top, hcard, upperPart_eq_self hn0]
    exact fun q hq => htp.trans (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
      (Nat.dvd_of_mem_primeFactors hq))
  · obtain ⟨H, hH, hHc⟩ := ih _ hlt (N := K) rfl (hN.subgroup K) hoddK t
    refine ⟨H.map K.subtype, inferInstance, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective, hHc, hnK,
      upperPart_mul_pow hp (not_le.1 htp) hK0]

/-- An odd-order Sylow-metacyclic group has a Sylow tower. -/
theorem hasSylowTower_of_odd [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] {N : Type} [Group N] [Finite N] (hN : SylowMetacyclic N)
    (hodd : Odd (Nat.card N)) : HasSylowTower N := fun t => by
  obtain ⟨H, hH, hc⟩ := exists_characteristic_upperPart _ rfl hN hodd t
  exact ⟨H, inferInstance, hc⟩

end CFSGOutside.ChillagSonn
