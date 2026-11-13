import CFSGOutside.HerzogK3Groups.Base

namespace CFSGOutside.HerzogK3Groups.Large

open CFSGOutside.Corpus CFSGOutside.Corpus.Open Finset

variable [CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy]

theorem four_A_core {n Q p : ℕ} (hn : 3 ≤ n) (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderA n Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 hQ hp hpQ
  obtain ⟨x, hx, hxp, hxd⟩ := X_minus hQ hp hpQ
  unfold orderA
  have hmem : ∀ i, 2 ≤ i → i ≤ n + 1 → i ∈ Icc 2 (n + 1) := by
    intro i h1 h2; simp only [Finset.mem_Icc]; omega
  have hP : ∀ ℓ k i, ℓ ∣ Q ^ k - 1 → k ∣ i → i ∈ Icc 2 (n + 1) →
      ℓ ∣ Q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1) := fun ℓ k i h hk hi =>
    ((dvd_pow_sub_of_dvd h hk).trans (Finset.dvd_prod_of_mem (fun i => Q ^ i - 1) hi)).trans
      (dvd_mul_left _ _)
  have h2X := hP (Q ^ 2 - 1) 2 2 dvd_rfl dvd_rfl (hmem 2 le_rfl (by omega))
  have hdQ : Nat.gcd (n + 1) (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hdX : Nat.gcd (n + 1) (Q - 1) ∣
      Q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1) :=
    hdQ.trans ((sub_one_dvd Q 2).trans h2X)
  have he : n * (n + 1) / 2 ≠ 0 := by
    have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    omega
  have hXne : Q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (Finset.prod_ne_zero_iff.2 fun i hi =>
      pow_sub_one_ne hQ (by simp only [Finset.mem_Icc] at hi; omega))
  refine four_div hXne hdX hp ha hb hx hap.symm hbp.symm hxp.symm hab ?_ ?_ ?_ ?_ ?_ ?_
  · intro h; exact hasq (h ▸ (dvd_mul_right x _).trans hxd)
  · intro h; exact hbsq (h ▸ (dvd_mul_right x _).trans hxd)
  · exact (coprime_char hp hpQ one_ne_zero (by omega) (Or.inl (by rwa [pow_one]))).mul_dvd_of_dvd_of_dvd
      (dvd_pow hpQ he |>.trans (dvd_mul_right _ _)) hdX
  · exact (coprime_of_not_dvd ha hdQ hanQ).mul_dvd_of_dvd_of_dvd
      (hP a 3 3 haQ dvd_rfl (hmem 3 (by omega) (by omega))) hdX
  · exact (coprime_of_not_dvd hb hdQ hbnQ).mul_dvd_of_dvd_of_dvd
      (hP b 4 4 hbQ dvd_rfl (hmem 4 (by omega) (by omega))) hdX
  · exact ((mul_dvd_mul_left x hdQ).trans hxd).trans h2X


theorem twP {n Q : ℕ} (hn : 2 ≤ n) (i : ℕ) (hi : 2 ≤ i) (hin : i ≤ n + 1) :
    (if Even i then Q ^ i - 1 else Q ^ i + 1) ∣
      ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) :=
  Finset.dvd_prod_of_mem (fun j => if Even j then Q ^ j - 1 else Q ^ j + 1)
    (by simp only [Finset.mem_Icc]; omega)

theorem twP2 {n Q : ℕ} (hn : 2 ≤ n) : Q ^ 2 - 1 ∣
    ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) := by
  have := twP (Q := Q) hn 2 le_rfl (by omega)
  rwa [if_pos even_two] at this

theorem twP3 {n Q : ℕ} (hn : 2 ≤ n) : Q ^ 3 + 1 ∣
    ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) := by
  have := twP (Q := Q) hn 3 (by norm_num) (by omega)
  rwa [if_neg (by decide)] at this

theorem twP4 {n Q : ℕ} (hn : 3 ≤ n) : Q ^ 4 - 1 ∣
    ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) := by
  have := twP (n := n) (Q := Q) (by omega) 4 (by norm_num) (by omega)
  rwa [if_pos (by decide)] at this

theorem twP5 {n Q : ℕ} (hn : 4 ≤ n) : Q ^ 5 + 1 ∣
    ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) := by
  have := twP (n := n) (Q := Q) (by omega) 5 (by norm_num) (by omega)
  rwa [if_neg (by decide)] at this

theorem twP_ne {n Q : ℕ} (hQ : 2 ≤ Q) :
    ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi => by
    split_ifs
    · exact pow_sub_one_ne hQ (by simp only [Finset.mem_Icc] at hi; omega)
    · exact Nat.succ_ne_zero _

theorem four_twistedA_ge3 {n Q p : ℕ} (hn : 3 ≤ n) (hQ : 3 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderTwistedA n Q).primeFactors.card := by
  obtain ⟨b, hb⟩ := exists_ppd hQ (show 3 ≤ 4 by norm_num)
  obtain ⟨c, hc⟩ := exists_ppd hQ (show 3 ≤ 6 by norm_num)
  obtain ⟨x, hx, hxp, hxd⟩ := X_plus hQ hp hpQ
  have hc3 : c ∣ Q ^ 3 + 1 := hc.dvd_add_of_double (k := 3) (by norm_num) (by omega)
  unfold orderTwistedA
  have hP : ∀ ℓ, ℓ ∣ ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) →
      ℓ ∣ Q ^ (n * (n + 1) / 2) *
        ∏ j ∈ Icc 2 (n + 1), (if Even j then Q ^ j - 1 else Q ^ j + 1) :=
    fun ℓ h => h.trans (dvd_mul_left _ _)
  have h2X := hP _ (twP2 (Q := Q) (by omega))
  have hdQ : Nat.gcd (n + 1) (Q + 1) ∣ Q + 1 := Nat.gcd_dvd_right _ _
  have hdsq : Nat.gcd (n + 1) (Q + 1) ∣ Q ^ 2 - 1 := hdQ.trans (add_one_dvd_sq (by omega))
  have hdX := hdsq.trans h2X
  have he : n * (n + 1) / 2 ≠ 0 := by
    have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    omega
  have hXne := mul_ne_zero (pow_ne_zero (n * (n + 1) / 2) (by omega : Q ≠ 0))
    (twP_ne (n := n) (by omega : 2 ≤ Q))
  have hbsq := hb.not_dvd_sq (by norm_num)
  have hcsq := hc.not_dvd_sq (by norm_num)
  have hxsq : x ∣ Q ^ 2 - 1 := (dvd_mul_right x _).trans hxd
  refine four_div hXne hdX hp hb.1 hc.1 hx (hb.ne_char (by norm_num) (by omega) hpQ).symm
    (hc.ne_char (by norm_num) (by omega) hpQ).symm hxp.symm (hb.ne hc (by norm_num) (by norm_num))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro h; exact hbsq (h ▸ hxsq)
  · intro h; exact hcsq (h ▸ hxsq)
  · exact (coprime_char hp hpQ one_ne_zero (by omega)
      (Or.inr (by rw [pow_one]; exact hdQ))).mul_dvd_of_dvd_of_dvd
      (dvd_pow hpQ he |>.trans (dvd_mul_right _ _)) hdX
  · exact (coprime_of_not_dvd hb.1 hdsq hbsq).mul_dvd_of_dvd_of_dvd
      (hP _ ((hb.2.1).trans (by simpa using twP4 (Q := Q) (by omega)))) hdX
  · exact (coprime_of_not_dvd hc.1 hdsq hcsq).mul_dvd_of_dvd_of_dvd
      (hP _ (hc3.trans (twP3 (Q := Q) (by omega)))) hdX
  · exact ((mul_dvd_mul_left x hdQ).trans hxd).trans h2X

theorem four_twistedA_two {n : ℕ} (hn : 4 ≤ n) :
    4 ≤ (orderTwistedA n 2).primeFactors.card := by
  unfold orderTwistedA
  have hP : ∀ ℓ, ℓ ∣ ∏ j ∈ Icc 2 (n + 1), (if Even j then 2 ^ j - 1 else 2 ^ j + 1) →
      ℓ ∣ 2 ^ (n * (n + 1) / 2) *
        ∏ j ∈ Icc 2 (n + 1), (if Even j then 2 ^ j - 1 else 2 ^ j + 1) :=
    fun ℓ h => h.trans (dvd_mul_left _ _)
  have hd3 : Nat.gcd (n + 1) (2 + 1) ∣ 3 := Nat.gcd_dvd_right _ _
  have h3P : 3 ∣ ∏ j ∈ Icc 2 (n + 1), (if Even j then 2 ^ j - 1 else 2 ^ j + 1) :=
    (by norm_num : 3 ∣ 2 ^ 2 - 1).trans (twP2 (by omega))
  have hdX := (hd3.trans h3P).trans (dvd_mul_left _ (2 ^ (n * (n + 1) / 2)))
  have he : n * (n + 1) / 2 ≠ 0 := by
    have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
    omega
  have hXne := mul_ne_zero (pow_ne_zero (n * (n + 1) / 2) (by omega : 2 ≠ 0))
    (twP_ne (n := n) (by omega : 2 ≤ 2))
  refine four_div (a := 2) (b := 3) (c := 5) (e := 11) hXne hdX Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_
  · exact ((Nat.Coprime.coprime_dvd_right hd3 (by norm_num : Nat.Coprime 2 3))).mul_dvd_of_dvd_of_dvd
      (dvd_pow_self 2 he |>.trans (dvd_mul_right _ _)) hdX
  · exact ((mul_dvd_mul_left 3 hd3).trans ((by norm_num : 3 * 3 ∣ 2 ^ 3 + 1).trans
      (twP3 (Q := 2) (by omega)))).trans (dvd_mul_left _ _)
  · exact ((Nat.Coprime.coprime_dvd_right hd3 (by norm_num : Nat.Coprime 5 3))).mul_dvd_of_dvd_of_dvd
      (hP _ ((by norm_num : 5 ∣ 2 ^ 4 - 1).trans (twP4 (Q := 2) (by omega)))) hdX
  · exact ((Nat.Coprime.coprime_dvd_right hd3 (by norm_num : Nat.Coprime 11 3))).mul_dvd_of_dvd_of_dvd
      (hP _ ((by norm_num : 11 ∣ 2 ^ 5 + 1).trans (twP5 (Q := 2) (by omega)))) hdX

theorem four_B_core {n Q p : ℕ} (hn : 3 ≤ n) (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderBC n Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 hQ hp hpQ
  unfold orderBC
  have hmem : ∀ i, 1 ≤ i → i ≤ n → i ∈ Icc 1 n := by
    intro i h1 h2; simp only [Finset.mem_Icc]; omega
  have hP : ∀ ℓ k i, ℓ ∣ Q ^ k - 1 → k ∣ 2 * i → i ∈ Icc 1 n →
      ℓ ∣ Q ^ (n * n) * ∏ i ∈ Icc 1 n, (Q ^ (2 * i) - 1) := fun ℓ k i h hk hi =>
    ((dvd_pow_sub_of_dvd h hk).trans
      (Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) hi)).trans (dvd_mul_left _ _)
  have hdQ : Nat.gcd 2 (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
  have hd4 : Nat.gcd 2 (Q - 1) ∣ 4 := (Nat.gcd_dvd_left 2 _).trans (by norm_num)
  have hdX := hdQ.trans <| hP (Q - 1) 1 1 (by rw [pow_one]) (one_dvd _) (hmem 1 le_rfl (by omega))
  have he : n * n ≠ 0 := by positivity
  have hXne : Q ^ (n * n) * ∏ i ∈ Icc 1 n, (Q ^ (2 * i) - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (Finset.prod_ne_zero_iff.2 fun i hi =>
      pow_sub_one_ne hQ (by simp only [Finset.mem_Icc] at hi; omega))
  exact four_fixed hXne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc
    (dvd_pow hpQ he |>.trans (dvd_mul_right _ _))
    (hP a 3 3 haQ (by norm_num) (hmem 3 (by omega) hn))
    (hP b 4 2 hbQ (by norm_num) (hmem 2 (by omega) (by omega)))
    (hP c 6 3 hcQ (by norm_num) (hmem 3 (by omega) hn))
    (coprime_char hp hpQ one_ne_zero (by omega) (Or.inl (by rw [pow_one]; exact hdQ)))
    (coprime_of_dvd_four ha ha2 hd4) (coprime_of_dvd_four hb hb2 hd4)
    (coprime_of_dvd_four hc hc2 hd4)

theorem four_D_core {n Q p : ℕ} (hn : 4 ≤ n) (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    4 ≤ (orderD n Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 hQ hp hpQ
  unfold orderD
  have hmem : ∀ i, 1 ≤ i → i ≤ n - 1 → i ∈ Icc 1 (n - 1) := by
    intro i h1 h2; simp only [Finset.mem_Icc]; omega
  have hP : ∀ ℓ k i, ℓ ∣ Q ^ k - 1 → k ∣ 2 * i → i ∈ Icc 1 (n - 1) →
      ℓ ∣ Q ^ (n * (n - 1)) * (Q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) :=
    fun ℓ k i h hk hi =>
    ((dvd_pow_sub_of_dvd h hk).trans
      (Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) hi)).trans (dvd_mul_left _ _)
  have hdQ : Nat.gcd 4 (Q ^ n - 1) ∣ Q ^ n - 1 := Nat.gcd_dvd_right _ _
  have hd4 : Nat.gcd 4 (Q ^ n - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hdX : Nat.gcd 4 (Q ^ n - 1) ∣
      Q ^ (n * (n - 1)) * (Q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) :=
    hdQ.trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
  have he : n * (n - 1) ≠ 0 := by
    have : 1 ≤ n - 1 := by omega
    positivity
  have hXne : Q ^ (n * (n - 1)) * (Q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_sub_one_ne hQ (by omega)))
      (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_sub_one_ne hQ (by simp only [Finset.mem_Icc] at hi; omega))
  exact four_fixed hXne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc
    ((dvd_pow hpQ he).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
    (hP a 3 3 haQ (by norm_num) (hmem 3 (by omega) (by omega)))
    (hP b 4 2 hbQ (by norm_num) (hmem 2 (by omega) (by omega)))
    (hP c 6 3 hcQ (by norm_num) (hmem 3 (by omega) (by omega)))
    (coprime_char hp hpQ (by omega) (by omega) (Or.inl hdQ))
    (coprime_of_dvd_four ha ha2 hd4) (coprime_of_dvd_four hb hb2 hd4)
    (coprime_of_dvd_four hc hc2 hd4)

theorem four_twistedD_core {n Q p : ℕ} (hn : 4 ≤ n) (hQ : 2 ≤ Q) (hp : p.Prime)
    (hpQ : p ∣ Q) : 4 ≤ (orderTwistedD n Q).primeFactors.card := by
  obtain ⟨a, b, c, ha, hb, hc, haQ, hbQ, hcQ, hab, hac, hbc, hap, hbp, hcp, ha2, hb2, hc2,
    hanQ, hbnQ, hcnQ, hasq, hbsq, hcsq⟩ := supply3 hQ hp hpQ
  unfold orderTwistedD
  have hmem : ∀ i, 1 ≤ i → i ≤ n - 1 → i ∈ Icc 1 (n - 1) := by
    intro i h1 h2; simp only [Finset.mem_Icc]; omega
  have hP : ∀ ℓ k i, ℓ ∣ Q ^ k - 1 → k ∣ 2 * i → i ∈ Icc 1 (n - 1) →
      ℓ ∣ Q ^ (n * (n - 1)) * (Q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) :=
    fun ℓ k i h hk hi =>
    ((dvd_pow_sub_of_dvd h hk).trans
      (Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) hi)).trans (dvd_mul_left _ _)
  have hdQ : Nat.gcd 4 (Q ^ n + 1) ∣ Q ^ n + 1 := Nat.gcd_dvd_right _ _
  have hd4 : Nat.gcd 4 (Q ^ n + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hdX : Nat.gcd 4 (Q ^ n + 1) ∣
      Q ^ (n * (n - 1)) * (Q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) :=
    hdQ.trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
  have he : n * (n - 1) ≠ 0 := by
    have : 1 ≤ n - 1 := by omega
    positivity
  have hXne : Q ^ (n * (n - 1)) * (Q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (Q ^ (2 * i) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) (Nat.succ_ne_zero _))
      (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_sub_one_ne hQ (by simp only [Finset.mem_Icc] at hi; omega))
  exact four_fixed hXne hdX hp ha hb hc hap.symm hbp.symm hcp.symm hab hac hbc
    ((dvd_pow hpQ he).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))
    (hP a 3 3 haQ (by norm_num) (hmem 3 (by omega) (by omega)))
    (hP b 4 2 hbQ (by norm_num) (hmem 2 (by omega) (by omega)))
    (hP c 6 3 hcQ (by norm_num) (hmem 3 (by omega) (by omega)))
    (coprime_char hp hpQ (by omega) (by omega) (Or.inr hdQ))
    (coprime_of_dvd_four ha ha2 hd4) (coprime_of_dvd_four hb hb2 hd4)
    (coprime_of_dvd_four hc hc2 hd4)

end CFSGOutside.HerzogK3Groups.Large
