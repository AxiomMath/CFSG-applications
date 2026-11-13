import Mathlib
import CFSGOutside.HerzogK3Groups.Small

namespace CFSGOutside.HerzogK3Groups.Rest

open CFSGOutside.Corpus.Open CFSGOutside.HerzogK3Groups.Large CFSGOutside.HerzogK3Groups.Small Finset

variable [CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy]

theorem four_suzuki (m : ℕ) (hm : 1 ≤ m) : 4 ≤ (orderSuzuki (2 ^ (2 * m + 1))).primeFactors.card := by
  set Q := 2 ^ (2 * m + 1) with hQ
  set R := 2 ^ (m + 1) with hR
  have hR2 : R ^ 2 = 2 * Q := by
    rw [hR, hQ, ← pow_mul, ← pow_succ']
    congr 1
    ring
  have hRQ : R < Q := by
    rw [hR, hQ]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hQ8 : 8 ≤ Q := by
    rw [hQ]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hR4 : 4 ≤ R := by
    rw [hR]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQeven : 2 ∣ Q := by
    rw [hQ]
    exact dvd_pow_self 2 (by omega)
  have hReven : 2 ∣ R := by
    rw [hR]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨s, hs⟩ : ∃ s, Q = R + s := ⟨Q - R, by omega⟩
  obtain ⟨cQ, hcQ⟩ := hQeven
  obtain ⟨cR, hcR⟩ := hReven
  have hs2 : s = 2 * (cQ - cR) := by omega
  have hprod : (Q + R + 1) * (s + 1) = Q ^ 2 + 1 := by
    have h1 : R ^ 2 = 2 * (R + s) := by rw [hR2, hs]
    nlinarith [h1, hs]
  set u := Q + R + 1 with hu
  set v := s + 1 with hv
  have hu1 : u ≠ 1 := by omega
  have hv1 : v ≠ 1 := by omega
  have hupr : u.minFac.Prime := Nat.minFac_prime hu1
  have hvpr : v.minFac.Prime := Nat.minFac_prime hv1
  have hxpr : (Q - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have huo : ¬ 2 ∣ u := by omega
  have hvo : ¬ 2 ∣ v := by omega
  have hxo : ¬ 2 ∣ Q - 1 := by omega
  have hu2 : u.minFac ≠ 2 := fun h => huo (h ▸ Nat.minFac_dvd u)
  have hv2 : v.minFac ≠ 2 := fun h => hvo (h ▸ Nat.minFac_dvd v)
  have hx2 : (Q - 1).minFac ≠ 2 := fun h => hxo (h ▸ Nat.minFac_dvd _)
  have huv : u.minFac ≠ v.minFac := by
    intro h
    have h1 : u.minFac ∣ u := Nat.minFac_dvd u
    have h2 : u.minFac ∣ v := h ▸ Nat.minFac_dvd v
    have h3 : u.minFac ∣ u - v := Nat.dvd_sub h1 h2
    rw [show u - v = 2 * R by omega] at h3
    rcases (Nat.Prime.dvd_mul hupr).1 h3 with h4 | h4
    · exact hu2 ((Nat.prime_dvd_prime_iff_eq hupr Nat.prime_two).1 h4)
    · have h5 : u.minFac ∣ 2 := hupr.dvd_of_dvd_pow (n := m + 1) (by rwa [← hR])
      exact hu2 ((Nat.prime_dvd_prime_iff_eq hupr Nat.prime_two).1 h5)
  have hxQ : (Q - 1).minFac ∣ Q ^ 2 + 1 → False := by
    intro h2
    have h1 : (Q - 1).minFac ∣ Q - 1 := Nat.minFac_dvd _
    have h3 : (Q - 1).minFac ∣ (Q ^ 2 + 1) - (Q - 1) * (Q + 1) := Nat.dvd_sub h2 (h1.mul_right _)
    have e : (Q ^ 2 + 1) - (Q - 1) * (Q + 1) = 2 := by
      have : (Q - 1) * (Q + 1) = Q ^ 2 - 1 := (sq_sub_one_eq (by omega)).symm
      rw [this]
      have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    rw [e] at h3
    exact hx2 ((Nat.prime_dvd_prime_iff_eq hxpr Nat.prime_two).1 h3)
  have huQ : u.minFac ∣ Q ^ 2 + 1 := by
    rw [← hprod]
    exact (Nat.minFac_dvd u).mul_right _
  have hvQ : v.minFac ∣ Q ^ 2 + 1 := by
    rw [← hprod]
    exact (Nat.minFac_dvd v).mul_left _
  have hN : orderSuzuki Q ≠ 0 := by
    unfold orderSuzuki
    have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) (by omega)
  refine four_nat hN Nat.prime_two hxpr hupr hvpr (Ne.symm hx2) (Ne.symm hu2) (Ne.symm hv2)
    (fun h => hxQ (h ▸ huQ)) (fun h => hxQ (h ▸ hvQ)) huv ?_ ?_ ?_ ?_ <;> unfold orderSuzuki
  · exact (((Dvd.intro cQ (by omega) : 2 ∣ Q).trans (dvd_pow_self Q (by norm_num))).mul_right _).mul_right _
  · exact (Nat.minFac_dvd _).mul_left _
  · exact (huQ.mul_left _).mul_right _
  · exact (hvQ.mul_left _).mul_right _

theorem three_pow_mod_eight (c : ℕ) : 3 ^ c % 8 = 1 ∨ 3 ^ c % 8 = 3 := by
  induction c with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem four_ree (m : ℕ) (hm : 1 ≤ m) : 4 ≤ (orderRee (3 ^ (2 * m + 1))).primeFactors.card := by
  set Q := 3 ^ (2 * m + 1) with hQ
  have hQ27 : 27 ≤ Q := by
    rw [hQ]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ3 : 3 ∣ Q := dvd_pow_self 3 (by omega)
  have hQ8 : Q % 8 = 3 := by
    rw [hQ, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hQ1 : Q % 3 = 0 := Nat.mod_eq_zero_of_dvd hQ3
  obtain ⟨ℓ, hℓ⟩ := exists_ppd (show 3 ≤ Q by omega) (show 3 ≤ 6 by norm_num)
  have hℓH : ℓ ∣ Q ^ 3 + 1 := Ppd.dvd_add_of_double (k := 3) hℓ (by norm_num) (by omega)
  obtain ⟨w, hw, hw2, hwQ⟩ := exists_odd_prime_of_not_two_pow (n := Q + 1) (by omega) (by
    intro a ha
    rcases Nat.lt_or_ge a 3 with h | h
    · interval_cases a <;> omega
    · have := Nat.pow_dvd_pow 2 h
      norm_num at this
      omega)
  have hw3 : w ≠ 3 := by
    rintro rfl
    omega
  have hwG : w ∣ Q ^ 2 - 1 := hwQ.trans (add_one_dvd_sq (by omega))
  have hwH : w ∣ Q ^ 3 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow Q 1 (show Odd 3 by decide)
    simpa using hwQ.trans this
  have h2 : 2 ∣ Q - 1 := by omega
  have hN : orderRee Q ≠ 0 := by
    unfold orderRee
    exact mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) (by omega)
  refine four_nat hN Nat.prime_three Nat.prime_two hw hℓ.1 (by norm_num) (Ne.symm hw3)
    (hℓ.ne_char (by norm_num) (by omega) hQ3).symm (Ne.symm hw2)
    (hℓ.ne_two (by norm_num) (by omega)).symm (fun h => hℓ.not_dvd_sq (by norm_num) (h ▸ hwG))
    ?_ ?_ ?_ ?_ <;> unfold orderRee
  · exact ((hQ3.trans (dvd_pow_self Q (by norm_num))).mul_right _).mul_right _
  · exact h2.mul_left _
  · exact (hwH.mul_left _).mul_right _
  · exact (hℓH.mul_left _).mul_right _

end CFSGOutside.HerzogK3Groups.Rest
