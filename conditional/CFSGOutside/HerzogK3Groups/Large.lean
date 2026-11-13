import CFSGOutside.HerzogK3Groups.Classical

syntax "dvd_prod" : tactic

macro_rules
  | `(tactic| dvd_prod) => `(tactic| first
      | with_reducible exact dvd_rfl
      | (with_reducible refine Dvd.dvd.mul_right ?_ _; dvd_prod)
      | (with_reducible refine Dvd.dvd.mul_left ?_ _; dvd_prod))

namespace CFSGOutside.HerzogK3Groups.Large

open CFSGOutside.Corpus CFSGOutside.Corpus.Open Finset

variable [CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy]

theorem four_E8_core {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderE8 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, -⟩ :=
    supply3 hQ hp hpQ
  have hQ0 : Q ≠ 0 := by omega
  have hne : orderE8 Q ≠ 0 := by unfold orderE8; simp [hQ0, pow_sub_one_ne hQ]
  have := four_fixed (X := orderE8 Q) (d := 1) hne (one_dvd _) hp ha hb hc hap.symm hbp.symm
    hcp.symm hab hac hbc ?_ ?_ ?_ ?_ (Nat.coprime_one_right _) (Nat.coprime_one_right _)
    (Nat.coprime_one_right _) (Nat.coprime_one_right _)
  · rwa [Nat.div_one] at this
  · exact (dvd_pow hpQ (by norm_num : 120 ≠ 0)).trans
      (by unfold orderE8; dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 12)).trans
      (by unfold orderE8; dvd_prod)
  · exact (dvd_pow_sub_of_dvd hbQ (by norm_num : 4 ∣ 8)).trans
      (by unfold orderE8; dvd_prod)
  · exact (dvd_pow_sub_of_dvd hcQ (by norm_num : 6 ∣ 12)).trans
      (by unfold orderE8; dvd_prod)

theorem four_F4_core {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderF4 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, -⟩ :=
    supply3 hQ hp hpQ
  have hQ0 : Q ≠ 0 := by omega
  have hne : orderF4 Q ≠ 0 := by unfold orderF4; simp [hQ0, pow_sub_one_ne hQ]
  have := four_fixed (X := orderF4 Q) (d := 1) hne (one_dvd _) hp ha hb hc hap.symm hbp.symm
    hcp.symm hab hac hbc ?_ ?_ ?_ ?_ (Nat.coprime_one_right _) (Nat.coprime_one_right _)
    (Nat.coprime_one_right _) (Nat.coprime_one_right _)
  · rwa [Nat.div_one] at this
  · exact (dvd_pow hpQ (by norm_num : 24 ≠ 0)).trans
      (by unfold orderF4; dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 12)).trans
      (by unfold orderF4; dvd_prod)
  · exact (dvd_pow_sub_of_dvd hbQ (by norm_num : 4 ∣ 8)).trans
      (by unfold orderF4; dvd_prod)
  · exact (dvd_pow_sub_of_dvd hcQ (by norm_num : 6 ∣ 12)).trans
      (by unfold orderF4; dvd_prod)

theorem four_E6_core {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderE6 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, -⟩ := supply3 hQ hp hpQ
  have hQ0 : Q ≠ 0 := by omega
  have hdQ : Nat.gcd 3 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hne : Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 - 1) *
      (Q ^ 2 - 1) ≠ 0 := by simp [hQ0, pow_sub_one_ne hQ]
  have hdX : Nat.gcd 3 (Q - 1) ∣ Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) *
      (Q ^ 6 - 1) * (Q ^ 5 - 1) * (Q ^ 2 - 1) :=
    (hdQ.trans (sub_one_dvd Q 2)).trans
      (by dvd_prod)
  unfold orderE6
  refine four_fixed hne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc ?_ ?_ ?_ ?_
    (coprime_char hp hpQ one_ne_zero (by omega) (Or.inl (by rw [pow_one]; exact hdQ)))
    (coprime_of_not_dvd ha hdQ hanQ) (coprime_of_not_dvd hb hdQ hbnQ)
    (coprime_of_not_dvd hc hdQ hcnQ)
  · exact (dvd_pow hpQ (by norm_num : 36 ≠ 0)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 12)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hbQ (by norm_num : 4 ∣ 8)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hcQ (by norm_num : 6 ∣ 6)).trans
      (by dvd_prod)

theorem four_E7_core {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderE7 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, -⟩ := supply3 hQ hp hpQ
  have hQ0 : Q ≠ 0 := by omega
  have hdQ : Nat.gcd 2 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hne : Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) * (Q ^ 8 - 1) *
      (Q ^ 6 - 1) * (Q ^ 2 - 1) ≠ 0 := by simp [hQ0, pow_sub_one_ne hQ]
  have hdX : Nat.gcd 2 (Q - 1) ∣ Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) *
      (Q ^ 10 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
    (hdQ.trans (sub_one_dvd Q 2)).trans
      (by dvd_prod)
  unfold orderE7
  refine four_fixed hne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc ?_ ?_ ?_ ?_
    (coprime_char hp hpQ one_ne_zero (by omega) (Or.inl (by rw [pow_one]; exact hdQ)))
    (coprime_of_not_dvd ha hdQ hanQ) (coprime_of_not_dvd hb hdQ hbnQ)
    (coprime_of_not_dvd hc hdQ hcnQ)
  · exact (dvd_pow hpQ (by norm_num : 63 ≠ 0)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 6)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hbQ (by norm_num : 4 ∣ 8)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hcQ (by norm_num : 6 ∣ 6)).trans
      (by dvd_prod)

theorem four_twistedE6_ge3 {Q p : ℕ} (hQ : 3 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderTwistedE6 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 (by omega) hp hpQ
  have hcsq := hcsq hQ
  have hQ0 : Q ≠ 0 := by omega
  have hQ2 : 2 ≤ Q := by omega
  have hdQ : Nat.gcd 3 (Q + 1) ∣ Q + 1 := Nat.gcd_dvd_right _ _
  have hdsq : Nat.gcd 3 (Q + 1) ∣ Q ^ 2 - 1 := hdQ.trans (add_one_dvd_sq (by omega))
  have hne : Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 + 1) *
      (Q ^ 2 - 1) ≠ 0 := by simp [hQ0, pow_sub_one_ne hQ2]
  have hdX : Nat.gcd 3 (Q + 1) ∣ Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) *
      (Q ^ 6 - 1) * (Q ^ 5 + 1) * (Q ^ 2 - 1) :=
    hdsq.trans (by dvd_prod)
  unfold orderTwistedE6
  refine four_fixed hne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc ?_ ?_ ?_ ?_
    (coprime_char hp hpQ one_ne_zero (by omega) (Or.inr (by rw [pow_one]; exact hdQ)))
    (coprime_of_not_dvd ha hdsq hasq) (coprime_of_not_dvd hb hdsq hbsq)
    (coprime_of_not_dvd hc hdsq hcsq)
  · exact (dvd_pow hpQ (by norm_num : 36 ≠ 0)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 12)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hbQ (by norm_num : 4 ∣ 8)).trans
      (by dvd_prod)
  · exact (dvd_pow_sub_of_dvd hcQ (by norm_num : 6 ∣ 6)).trans
      (by dvd_prod)

theorem four_twistedE6_two : 4 ≤ (orderTwistedE6 2).primeFactors.card :=
  four_nat (a := 2) (b := 5) (c := 7) (e := 13) (by norm_num [orderTwistedE6])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [orderTwistedE6]) (by norm_num [orderTwistedE6])
    (by norm_num [orderTwistedE6]) (by norm_num [orderTwistedE6])

theorem four_trialityD4_ge3 {Q p : ℕ} (hQ : 3 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderTrialityD4 Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 (by omega) hp hpQ
  have hcsq := hcsq hQ
  obtain ⟨x, hx, hxp, hxd⟩ := X_minus (by omega : 2 ≤ Q) hp hpQ
  have hxsq : x ∣ Q ^ 2 - 1 := (dvd_mul_right x _).trans hxd
  have hQ0 : Q ≠ 0 := by omega
  have hne : orderTrialityD4 Q ≠ 0 := by
    unfold orderTrialityD4; simp [hQ0, pow_sub_one_ne (by omega : 2 ≤ Q)]
  refine four_nat hne hp ha hc hx hap.symm hcp.symm hxp.symm hac ?_ ?_ ?_ ?_ ?_ ?_
  · intro h; exact hasq (h ▸ hxsq)
  · intro h; exact hcsq (h ▸ hxsq)
  · exact (dvd_pow hpQ (by norm_num : 12 ≠ 0)).trans
      (by unfold orderTrialityD4; dvd_prod)
  · exact (dvd_pow_sub_of_dvd haQ (by norm_num : 3 ∣ 6)).trans
      (by unfold orderTrialityD4; dvd_prod)
  · exact hcQ.trans
      (by unfold orderTrialityD4; dvd_prod)
  · exact hxsq.trans
      (by unfold orderTrialityD4; dvd_prod)

theorem four_trialityD4_two : 4 ≤ (orderTrialityD4 2).primeFactors.card :=
  four_nat (a := 2) (b := 3) (c := 7) (e := 13) (by norm_num [orderTrialityD4])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [orderTrialityD4]) (by norm_num [orderTrialityD4])
    (by norm_num [orderTrialityD4]) (by norm_num [orderTrialityD4])

theorem four_tits : 4 ≤ orderTits.primeFactors.card :=
  four_nat (a := 2) (b := 3) (c := 5) (e := 13) (by norm_num [orderTits])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [orderTits]) (by norm_num [orderTits])
    (by norm_num [orderTits]) (by norm_num [orderTits])

theorem four_reeF4 (m : ℕ) (hm : 1 ≤ m) :
    4 ≤ (orderTwistedF4 (2 ^ (2 * m + 1))).primeFactors.card := by
  set Q := 2 ^ (2 * m + 1) with hQdef
  have hQ3 : 3 ≤ Q := by
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpQ : 2 ∣ Q := dvd_pow_self 2 (by omega)
  obtain ⟨b, hb⟩ := exists_ppd hQ3 (show 3 ≤ 4 by norm_num)
  obtain ⟨c, hc⟩ := exists_ppd hQ3 (show 3 ≤ 6 by norm_num)
  obtain ⟨e, he⟩ := exists_ppd hQ3 (show 3 ≤ 12 by norm_num)
  have hc3 : c ∣ Q ^ 3 + 1 := hc.dvd_add_of_double (k := 3) (by norm_num) (by omega)
  have he6 : e ∣ Q ^ 6 + 1 := he.dvd_add_of_double (k := 6) (by norm_num) (by omega)
  have hQ0 : Q ≠ 0 := by omega
  have hne : orderTwistedF4 Q ≠ 0 := by
    unfold orderTwistedF4
    simp [hQ0, pow_sub_one_ne (by omega : 2 ≤ Q)]
    omega
  refine four_nat hne Nat.prime_two hb.1 hc.1 he.1
    (hb.ne_char (by norm_num) (by omega) hpQ).symm (hc.ne_char (by norm_num) (by omega) hpQ).symm
    (he.ne_char (by norm_num) (by omega) hpQ).symm (hb.ne hc (by norm_num) (by norm_num))
    (hb.ne he (by norm_num) (by norm_num)) (hc.ne he (by norm_num) (by norm_num)) ?_ ?_ ?_ ?_
  · exact (dvd_pow hpQ (by norm_num : 12 ≠ 0)).trans
      (by unfold orderTwistedF4; dvd_prod)
  · exact hb.2.1.trans
      (by unfold orderTwistedF4; dvd_prod)
  · exact hc3.trans
      (by unfold orderTwistedF4; dvd_prod)
  · exact he6.trans
      (by unfold orderTwistedF4; dvd_prod)

theorem four_A (n : ℕ) (hn : 3 ≤ n) (q : TauCeti.PrimePower) :
    4 ≤ (orderA n q.card).primeFactors.card :=
  four_A_core hn (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_twistedA (n : ℕ) (hn : 3 ≤ n) (q : TauCeti.PrimePower)
    (hq : 3 ≤ q.card ∨ 4 ≤ n) : 4 ≤ (orderTwistedA n q.card).primeFactors.card := by
  by_cases h3 : 3 ≤ q.card
  · exact four_twistedA_ge3 hn h3 q.prime_p (char_dvd_card q)
  · have h2 : q.card = 2 := by have := card_ge_two q; omega
    rw [h2]
    exact four_twistedA_two (hq.resolve_left h3)

theorem four_B (n : ℕ) (hn : 3 ≤ n) (q : TauCeti.PrimePower) :
    4 ≤ (orderBC n q.card).primeFactors.card :=
  four_B_core hn (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_D (n : ℕ) (hn : 4 ≤ n) (q : TauCeti.PrimePower) :
    4 ≤ (orderD n q.card).primeFactors.card :=
  four_D_core hn (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_twistedD (n : ℕ) (hn : 4 ≤ n) (q : TauCeti.PrimePower) :
    4 ≤ (orderTwistedD n q.card).primeFactors.card :=
  four_twistedD_core hn (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_E6 (q : TauCeti.PrimePower) : 4 ≤ (orderE6 q.card).primeFactors.card :=
  four_E6_core (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_E7 (q : TauCeti.PrimePower) : 4 ≤ (orderE7 q.card).primeFactors.card :=
  four_E7_core (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_E8 (q : TauCeti.PrimePower) : 4 ≤ (orderE8 q.card).primeFactors.card :=
  four_E8_core (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_F4 (q : TauCeti.PrimePower) : 4 ≤ (orderF4 q.card).primeFactors.card :=
  four_F4_core (card_ge_two q) q.prime_p (char_dvd_card q)

theorem four_twistedE6 (q : TauCeti.PrimePower) :
    4 ≤ (orderTwistedE6 q.card).primeFactors.card := by
  by_cases h3 : 3 ≤ q.card
  · exact four_twistedE6_ge3 h3 q.prime_p (char_dvd_card q)
  · have h2 : q.card = 2 := by have := card_ge_two q; omega
    rw [h2]
    exact four_twistedE6_two

theorem four_trialityD4 (q : TauCeti.PrimePower) :
    4 ≤ (orderTrialityD4 q.card).primeFactors.card := by
  by_cases h3 : 3 ≤ q.card
  · exact four_trialityD4_ge3 h3 q.prime_p (char_dvd_card q)
  · have h2 : q.card = 2 := by have := card_ge_two q; omega
    rw [h2]
    exact four_trialityD4_two

end CFSGOutside.HerzogK3Groups.Large
