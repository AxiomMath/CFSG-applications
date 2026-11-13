import Mathlib
import CFSGOutside.HerzogK3Groups.Base

namespace CFSGOutside.HerzogK3Groups.Small

open CFSGOutside.Corpus.Open CFSGOutside.HerzogK3Groups.Large Finset

variable [CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy]

theorem exists_odd_prime_of_not_two_pow {n : ℕ} (h0 : n ≠ 0) (h : ∀ a, n ≠ 2 ^ a) :
    ∃ x, x.Prime ∧ x ≠ 2 ∧ x ∣ n := by
  by_contra hc
  push_neg at hc
  apply h n.primeFactorsList.length
  apply Nat.eq_prime_pow_of_unique_prime_dvd h0
  intro d hd hdn
  by_contra hne
  exact hc d hd hne hdn

theorem exists_odd_prime_sq_sub_one {Q : ℕ} (hodd : Odd Q) (h5 : 5 ≤ Q) :
    ∃ x, x.Prime ∧ x ≠ 2 ∧ x ∣ Q ^ 2 - 1 := by
  by_contra hc
  push_neg at hc
  have key : ∀ M, M ∣ Q ^ 2 - 1 → M ≠ 0 → ∃ a, M = 2 ^ a := by
    intro M hM hM0
    refine ⟨M.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd hM0 ?_⟩
    intro d hd hdM
    by_contra hne
    exact hc d hd hne (hdM.trans hM)
  obtain ⟨a, ha⟩ := key (Q - 1) (sub_one_dvd Q 2) (by omega)
  obtain ⟨b, hb⟩ := key (Q + 1) (add_one_dvd_sq (by omega)) (by omega)
  have h4a : 4 ∣ Q - 1 := by
    rw [ha]
    rcases Nat.lt_or_ge a 2 with h | h
    · interval_cases a <;> omega
    · have := Nat.pow_dvd_pow 2 h
      norm_num at this
      exact this
  have h4b : 4 ∣ Q + 1 := by
    rw [hb]
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b <;> omega
    · have := Nat.pow_dvd_pow 2 h
      norm_num at this
      exact this
  omega

theorem four_quad_even {Q e H d ℓ : ℕ} (hQ : 4 ≤ Q) (hQe : Even Q) (he : e ≠ 0) (hH : H ≠ 0)
    (hdG : d ∣ Q ^ 2 - 1) (hdH : d ∣ H) (hℓ : ℓ.Prime) (hℓH : ℓ ∣ H)
    (hℓG : ¬ ℓ ∣ Q ^ 2 - 1) (hℓ2 : ℓ ≠ 2) :
    4 ≤ (Q ^ e * ((Q ^ 2 - 1) * H) / d).primeFactors.card := by
  have h2Q : 2 ∣ Q := even_iff_two_dvd.1 hQe
  obtain ⟨c, hc⟩ := hQe
  have hG0 : Q ^ 2 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  have hX : Q ^ e * ((Q ^ 2 - 1) * H) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (mul_ne_zero hG0 hH)
  have hx : (Q - 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hy : (Q + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hxd : (Q - 1).minFac ∣ Q - 1 := Nat.minFac_dvd _
  have hyd : (Q + 1).minFac ∣ Q + 1 := Nat.minFac_dvd _
  have hx2 : (Q - 1).minFac ≠ 2 := by
    intro h
    rw [h] at hxd
    omega
  have hy2 : (Q + 1).minFac ≠ 2 := by
    intro h
    rw [h] at hyd
    omega
  have hxG : (Q - 1).minFac ∣ Q ^ 2 - 1 := hxd.trans (sub_one_dvd Q 2)
  have hyG : (Q + 1).minFac ∣ Q ^ 2 - 1 := hyd.trans (add_one_dvd_sq (by omega))
  have hxy : (Q - 1).minFac ≠ (Q + 1).minFac := by
    intro h
    have h2 : (Q - 1).minFac ∣ Q + 1 := h ▸ hyd
    have h3 : (Q - 1).minFac ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub h2 hxd
    rw [show Q + 1 - (Q - 1) = 2 by omega] at h3
    exact hx2 ((Nat.prime_dvd_prime_iff_eq hx Nat.prime_two).1 h3)
  have hd : d ∣ Q ^ e * ((Q ^ 2 - 1) * H) := hdG.trans ((dvd_mul_right _ _).trans (dvd_mul_left _ _))
  have h2e : 2 ∣ Q ^ e := h2Q.trans (dvd_pow_self Q he)
  refine four_div hX hd Nat.prime_two hx hy hℓ (Ne.symm hx2) (Ne.symm hy2) (Ne.symm hℓ2) hxy
    (fun h => hℓG (h ▸ hxG)) (fun h => hℓG (h ▸ hyG)) ?_ ?_ ?_ ?_
  · exact (mul_dvd_mul h2e hdG).trans ⟨H, by ring⟩
  · exact (mul_dvd_mul hxG hdH).trans (dvd_mul_left _ _)
  · exact (mul_dvd_mul hyG hdH).trans (dvd_mul_left _ _)
  · have := mul_dvd_mul hdG hℓH
    rw [mul_comm d ℓ] at this
    exact this.trans (dvd_mul_left _ _)

theorem four_quad_odd {Q e H d p ℓ : ℕ} (hQ : 5 ≤ Q) (hQo : Odd Q) (he : e ≠ 0) (hH : H ≠ 0)
    (hp : p.Prime) (hpQ : p ∣ Q) (hdG : d ∣ Q ^ 2 - 1) (hdH : d ∣ H) (hℓ : ℓ.Prime)
    (hℓH : ℓ ∣ H) (hℓG : ¬ ℓ ∣ Q ^ 2 - 1) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ p) :
    4 ≤ (Q ^ e * ((Q ^ 2 - 1) * H) / d).primeFactors.card := by
  obtain ⟨c, hc⟩ := hQo
  have hG0 : Q ^ 2 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  have hX : Q ^ e * ((Q ^ 2 - 1) * H) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (mul_ne_zero hG0 hH)
  obtain ⟨x, hx, hx2, hxG⟩ := exists_odd_prime_sq_sub_one ⟨c, hc⟩ hQ
  have h2G : 2 ∣ Q ^ 2 - 1 := by
    have : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := sq_sub_one_eq (by omega)
    rw [this]
    exact Dvd.dvd.mul_right ⟨c, by omega⟩ _
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpG : ¬ p ∣ Q ^ 2 - 1 := fun h =>
    not_dvd_sub_one (Nat.one_le_pow _ _ (by omega)) (dvd_pow hpQ (by norm_num)) h hp
  have hd : d ∣ Q ^ e * ((Q ^ 2 - 1) * H) := hdG.trans ((dvd_mul_right _ _).trans (dvd_mul_left _ _))
  have hpe : p ∣ Q ^ e := hpQ.trans (dvd_pow_self Q he)
  refine four_div hX hd hp Nat.prime_two hx hℓ hp2 (fun h => hpG (h ▸ hxG)) (Ne.symm hℓp)
    (Ne.symm hx2) (Ne.symm hℓ2) (fun h => hℓG (h ▸ hxG)) ?_ ?_ ?_ ?_
  · exact (mul_dvd_mul hpe hdG).trans ⟨H, by ring⟩
  · exact (mul_dvd_mul h2G hdH).trans (dvd_mul_left _ _)
  · exact (mul_dvd_mul hxG hdH).trans (dvd_mul_left _ _)
  · have := mul_dvd_mul hdG hℓH
    rw [mul_comm d ℓ] at this
    exact this.trans (dvd_mul_left _ _)

theorem orderA_two (Q : ℕ) :
    orderA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / Nat.gcd 3 (Q - 1) := by
  have : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  simp only [orderA, this, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]

theorem orderTwistedA_two (Q : ℕ) :
    orderTwistedA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) / Nat.gcd 3 (Q + 1) := by
  have : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  have e2 : Even 2 := by decide
  have e3 : ¬ Even 3 := by decide
  simp only [orderTwistedA, this, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3), if_pos e2,
    if_neg e3]
  all_goals norm_num

theorem orderBC_two (Q : ℕ) :
    orderBC 2 Q = Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) / Nat.gcd 2 (Q - 1) := by
  have : Finset.Icc 1 2 = {1, 2} := by decide
  simp only [orderBC, this, Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2)]
  all_goals norm_num

theorem four_A2 {Q p : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hQ : 4 ≤ Q) :
    4 ≤ (orderA 2 Q).primeFactors.card := by
  rw [orderA_two]
  obtain ⟨ℓ, hℓ⟩ := exists_ppd (show 3 ≤ Q by omega) (show 3 ≤ 3 by norm_num)
  have hdQ : Nat.gcd 3 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hdG : Nat.gcd 3 (Q - 1) ∣ Q ^ 2 - 1 := hdQ.trans (sub_one_dvd Q 2)
  have hdH : Nat.gcd 3 (Q - 1) ∣ Q ^ 3 - 1 := hdQ.trans (sub_one_dvd Q 3)
  have hH : Q ^ 3 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  rcases Nat.even_or_odd Q with he | ho
  · exact four_quad_even hQ he (by norm_num) hH hdG hdH hℓ.1 hℓ.2.1 (hℓ.not_dvd_sq le_rfl)
      (hℓ.ne_two (by norm_num) (by omega))
  · exact four_quad_odd (by obtain ⟨c, hc⟩ := ho; omega) ho (by norm_num) hH hp hpQ hdG hdH hℓ.1
      hℓ.2.1 (hℓ.not_dvd_sq le_rfl) (hℓ.ne_two (by norm_num) (by omega))
      (hℓ.ne_char (by norm_num) (by omega) hpQ)

theorem four_twistedA2 {Q p : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hQ : 4 ≤ Q) :
    4 ≤ (orderTwistedA 2 Q).primeFactors.card := by
  rw [orderTwistedA_two]
  obtain ⟨ℓ, hℓ⟩ := exists_ppd (show 3 ≤ Q by omega) (show 3 ≤ 6 by norm_num)
  have hdQ : Nat.gcd 3 (Q + 1) ∣ Q + 1 := Nat.gcd_dvd_right _ _
  have hdG : Nat.gcd 3 (Q + 1) ∣ Q ^ 2 - 1 := hdQ.trans (add_one_dvd_sq (by omega))
  have hdH : Nat.gcd 3 (Q + 1) ∣ Q ^ 3 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow Q 1 (show Odd 3 by decide)
    simpa using hdQ.trans this
  have hH : Q ^ 3 + 1 ≠ 0 := by positivity
  have hℓH : ℓ ∣ Q ^ 3 + 1 := Ppd.dvd_add_of_double (k := 3) hℓ (by norm_num) (by omega)
  rcases Nat.even_or_odd Q with he | ho
  · exact four_quad_even hQ he (by norm_num) hH hdG hdH hℓ.1 hℓH (hℓ.not_dvd_sq (by norm_num))
      (hℓ.ne_two (by norm_num) (by omega))
  · exact four_quad_odd (by obtain ⟨c, hc⟩ := ho; omega) ho (by norm_num) hH hp hpQ hdG hdH hℓ.1
      hℓH (hℓ.not_dvd_sq (by norm_num)) (hℓ.ne_two (by norm_num) (by omega))
      (hℓ.ne_char (by norm_num) (by omega) hpQ)

theorem four_B2 {Q p : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hQ : 4 ≤ Q) :
    4 ≤ (orderBC 2 Q).primeFactors.card := by
  rw [orderBC_two]
  obtain ⟨ℓ, hℓ⟩ := exists_ppd (show 3 ≤ Q by omega) (show 3 ≤ 4 by norm_num)
  have hdQ : Nat.gcd 2 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hdG : Nat.gcd 2 (Q - 1) ∣ Q ^ 2 - 1 := hdQ.trans (sub_one_dvd Q 2)
  have hdH : Nat.gcd 2 (Q - 1) ∣ Q ^ 4 - 1 := hdQ.trans (sub_one_dvd Q 4)
  have hH : Q ^ 4 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  rcases Nat.even_or_odd Q with he | ho
  · exact four_quad_even hQ he (by norm_num) hH hdG hdH hℓ.1 hℓ.2.1 (hℓ.not_dvd_sq (by norm_num))
      (hℓ.ne_two (by norm_num) (by omega))
  · exact four_quad_odd (by obtain ⟨c, hc⟩ := ho; omega) ho (by norm_num) hH hp hpQ hdG hdH hℓ.1
      hℓ.2.1 (hℓ.not_dvd_sq (by norm_num)) (hℓ.ne_two (by norm_num) (by omega))
      (hℓ.ne_char (by norm_num) (by omega) hpQ)

theorem four_G2 {Q p : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hQ : 3 ≤ Q) :
    4 ≤ (orderG2 Q).primeFactors.card := by
  obtain ⟨ℓ, hℓ⟩ := exists_ppd hQ (show 3 ≤ 6 by norm_num)
  have hH : Q ^ 6 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  rcases Nat.even_or_odd Q with he | ho
  · have := four_quad_even (e := 6) (d := 1) (H := Q ^ 6 - 1) (by
      obtain ⟨c, hc⟩ := he
      rcases Nat.lt_or_ge Q 4 with h | h
      · omega
      · exact h) he (by norm_num) hH (one_dvd _) (one_dvd _) hℓ.1 hℓ.2.1
      (hℓ.not_dvd_sq (by norm_num)) (hℓ.ne_two (by norm_num) (by omega))
    have e : orderG2 Q = Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 6 - 1)) := by unfold orderG2; ring
    rw [e]
    simpa using this
  · obtain ⟨a, ha⟩ := exists_ppd hQ (show 3 ≤ 3 by norm_num)
    have hN : orderG2 Q ≠ 0 := by
      unfold orderG2
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) hH)
        (pow_sub_one_ne (by omega) (by norm_num))
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨c, hc⟩ := ho
      omega
    have h2 : 2 ∣ Q ^ 6 - 1 := by
      have : 2 ∣ Q - 1 := by obtain ⟨c, hc⟩ := ho; exact ⟨c, by omega⟩
      exact this.trans (sub_one_dvd Q 6)
    refine four_nat hN hp Nat.prime_two ha.1 hℓ.1 hp2
      (ha.ne_char (by norm_num) (by omega) hpQ).symm (hℓ.ne_char (by norm_num) (by omega) hpQ).symm
      (ha.ne_two (by norm_num) (by omega)).symm (hℓ.ne_two (by norm_num) (by omega)).symm
      (ha.ne hℓ (by norm_num) (by norm_num)) ?_ ?_ ?_ ?_
    · unfold orderG2
      exact ((hpQ.trans (dvd_pow_self Q (by norm_num))).mul_right _).mul_right _
    · unfold orderG2
      exact ((h2.mul_left _)).mul_right _
    · unfold orderG2
      exact ((dvd_pow_sub_of_dvd ha.2.1 (by norm_num : 3 ∣ 6)).mul_left _).mul_right _
    · unfold orderG2
      exact ((hℓ.2.1).mul_left _).mul_right _

end CFSGOutside.HerzogK3Groups.Small
