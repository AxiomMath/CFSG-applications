import Mathlib
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy
import CFSGOutside.Corpus.Defs.LieOrder

namespace CFSGOutside.HerzogK3Groups.Large

open CFSGOutside.Corpus CFSGOutside.Corpus.Open Finset

theorem dvd_div_of_mul_dvd {m N D : ℕ} (h : m * D ∣ N) : m ∣ N / D := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  obtain ⟨k, hk⟩ := h
  rw [hk, show m * D * k = D * (m * k) by ring, Nat.mul_div_cancel_left _ hD]
  exact dvd_mul_right _ _

theorem sub_one_dvd (Q k : ℕ) : Q - 1 ∣ Q ^ k - 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · rcases k with _ | k <;> simp
  have h : 1 ≡ Q [MOD Q - 1] := (Nat.modEq_iff_dvd' hQ).2 dvd_rfl
  have := h.pow k
  rw [one_pow] at this
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hQ)).1 this

theorem sq_sub_one_eq {Q : ℕ} (hQ : 1 ≤ Q) : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
  have : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

theorem add_one_dvd_sq {Q : ℕ} (hQ : 1 ≤ Q) : Q + 1 ∣ Q ^ 2 - 1 :=
  ⟨Q - 1, by rw [sq_sub_one_eq hQ]; ring⟩

theorem card_ge_two (q : TauCeti.PrimePower) : 2 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)

theorem char_dvd_card (q : TauCeti.PrimePower) : q.p ∣ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact dvd_pow_self _ q.exponent_pos.ne'

theorem pow_sub_one_ne {Q k : ℕ} (hQ : 2 ≤ Q) (hk : k ≠ 0) : Q ^ k - 1 ≠ 0 := by
  have := Nat.one_lt_pow hk (by omega : 1 < Q)
  omega

theorem dvd_pow_sub_of_dvd {ℓ Q k j : ℕ} (h : ℓ ∣ Q ^ k - 1) (hkj : k ∣ j) : ℓ ∣ Q ^ j - 1 := by
  obtain ⟨m, rfl⟩ := hkj
  rw [pow_mul]
  exact h.trans (sub_one_dvd _ m)

theorem four_nat {N a b c e : ℕ} (hN : N ≠ 0) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (he : e.Prime) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e)
    (hce : c ≠ e) (ha' : a ∣ N) (hb' : b ∣ N) (hc' : c ∣ N) (he' : e ∣ N) :
    4 ≤ N.primeFactors.card := by
  have hsub : ({a, b, c, e} : Finset ℕ) ⊆ N.primeFactors := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rw [Nat.mem_primeFactors]
    rcases hr with rfl | rfl | rfl | rfl
    exacts [⟨ha, ha', hN⟩, ⟨hb, hb', hN⟩, ⟨hc, hc', hN⟩, ⟨he, he', hN⟩]
  have hcard : ({a, b, c, e} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbe]), Finset.card_pair hce]
  calc 4 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem four_div {X d a b c e : ℕ} (hX : X ≠ 0) (hd : d ∣ X) (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (he : e.Prime) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c)
    (hbe : b ≠ e) (hce : c ≠ e) (ha' : a * d ∣ X) (hb' : b * d ∣ X) (hc' : c * d ∣ X)
    (he' : e * d ∣ X) : 4 ≤ (X / d).primeFactors.card := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hX)
  have hN : X / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hX) hd) hd0).ne'
  exact four_nat hN ha hb hc he hab hac hae hbc hbe hce (dvd_div_of_mul_dvd ha')
    (dvd_div_of_mul_dvd hb') (dvd_div_of_mul_dvd hc') (dvd_div_of_mul_dvd he')

theorem four_fixed {X d p a b c : ℕ} (hX : X ≠ 0) (hd : d ∣ X) (hp : p.Prime) (ha : a.Prime)
    (hb : b.Prime) (hc : c.Prime) (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hpX : p ∣ X) (haX : a ∣ X) (hbX : b ∣ X) (hcX : c ∣ X)
    (cp : Nat.Coprime p d) (ca : Nat.Coprime a d) (cb : Nat.Coprime b d)
    (cc : Nat.Coprime c d) : 4 ≤ (X / d).primeFactors.card :=
  four_div hX hd hp ha hb hc hpa hpb hpc hab hac hbc (cp.mul_dvd_of_dvd_of_dvd hpX hd)
    (ca.mul_dvd_of_dvd_of_dvd haX hd) (cb.mul_dvd_of_dvd_of_dvd hbX hd)
    (cc.mul_dvd_of_dvd_of_dvd hcX hd)

theorem not_dvd_sub_one {ℓ M : ℕ} (hM : 1 ≤ M) (h1 : ℓ ∣ M) (h2 : ℓ ∣ M - 1) (hℓ : ℓ.Prime) :
    False := by
  have h3 : ℓ ∣ M - 1 + 1 := by rwa [Nat.sub_add_cancel hM]
  exact hℓ.ne_one (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h3))

theorem not_dvd_add_one {ℓ M : ℕ} (h1 : ℓ ∣ M) (h2 : ℓ ∣ M + 1) (hℓ : ℓ.Prime) : False :=
  hℓ.ne_one (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2))

def Ppd (Q n ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ ℓ ∣ Q ^ n - 1 ∧ ∀ k, 0 < k → k < n → ¬ℓ ∣ Q ^ k - 1

theorem exists_ppd [SL2MinimalFaithfulZsigmondy] {Q n : ℕ} (hQ : 3 ≤ Q) (hn : 3 ≤ n) : ∃ ℓ, Ppd Q n ℓ :=
  (SL2MinimalFaithfulZsigmondy.exists_primitive_prime_dvd_pow_sub_one hQ hn).imp fun _ h => h

theorem Ppd.ne_char {Q n ℓ p : ℕ} (h : Ppd Q n ℓ) (hn : n ≠ 0) (hQ : 1 ≤ Q) (hpQ : p ∣ Q) :
    ℓ ≠ p := by
  rintro rfl
  exact not_dvd_sub_one (Nat.one_le_pow _ _ hQ) (dvd_pow hpQ hn) h.2.1 h.1

theorem Ppd.ne {Q n m ℓ ℓ' : ℕ} (h : Ppd Q n ℓ) (h' : Ppd Q m ℓ') (hn : 0 < n) (hnm : n < m) :
    ℓ ≠ ℓ' := by
  rintro rfl
  exact h'.2.2 n hn hnm h.2.1

theorem Ppd.not_dvd_sq {Q n ℓ : ℕ} (h : Ppd Q n ℓ) (hn : 3 ≤ n) : ¬ ℓ ∣ Q ^ 2 - 1 :=
  h.2.2 2 (by norm_num) (by omega)

theorem Ppd.not_dvd_one {Q n ℓ : ℕ} (h : Ppd Q n ℓ) (hn : 2 ≤ n) : ¬ ℓ ∣ Q - 1 := by
  have := h.2.2 1 one_pos (by omega)
  rwa [pow_one] at this

theorem Ppd.ne_two {Q n ℓ : ℕ} (h : Ppd Q n ℓ) (hn : 2 ≤ n) (hQ : 1 ≤ Q) : ℓ ≠ 2 := by
  rintro rfl
  rcases Nat.even_or_odd Q with he | ho
  · exact not_dvd_sub_one (Nat.one_le_pow _ _ hQ)
      (dvd_pow (even_iff_two_dvd.1 he) (by omega)) h.2.1 Nat.prime_two
  · apply h.not_dvd_one hn
    obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩

theorem Ppd.dvd_add_of_double {Q k ℓ : ℕ} (h : Ppd Q (2 * k) ℓ) (hk : 0 < k) (hQ : 1 ≤ Q) :
    ℓ ∣ Q ^ k + 1 := by
  have e : Q ^ (2 * k) - 1 = (Q ^ k - 1) * (Q ^ k + 1) := by
    rw [show Q ^ (2 * k) = (Q ^ k) ^ 2 by ring]
    exact sq_sub_one_eq (Nat.one_le_pow _ _ (by omega))
  have h1 := h.2.1
  rw [e] at h1
  rcases (Nat.Prime.dvd_mul h.1).1 h1 with h2 | h2
  · exact absurd h2 (h.2.2 k hk (by omega))
  · exact h2

theorem coprime_of_dvd_four {ℓ d : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (hd : d ∣ 4) :
    Nat.Coprime ℓ d := by
  have h : Nat.Coprime ℓ (2 ^ 2) :=
    ((Nat.coprime_primes hℓ Nat.prime_two).2 h2).pow_right 2
  exact h.coprime_dvd_right (by simpa using hd)

theorem coprime_char {p Q m d : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hm : m ≠ 0) (hQ : 1 ≤ Q)
    (hd : d ∣ Q ^ m - 1 ∨ d ∣ Q ^ m + 1) : Nat.Coprime p d := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hpd
  rcases hd with hd | hd
  · exact not_dvd_sub_one (Nat.one_le_pow _ _ hQ) (dvd_pow hpQ hm) (hpd.trans hd) hp
  · exact not_dvd_add_one (dvd_pow hpQ hm) (hpd.trans hd) hp

theorem coprime_of_not_dvd {ℓ d M : ℕ} (hℓ : ℓ.Prime) (hd : d ∣ M) (h : ¬ ℓ ∣ M) :
    Nat.Coprime ℓ d :=
  (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun h' => h (h'.trans hd)

variable [SL2MinimalFaithfulZsigmondy]

theorem supply3 {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ a ∣ Q ^ 3 - 1 ∧ b ∣ Q ^ 4 - 1 ∧
      c ∣ Q ^ 6 - 1 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ p ∧ b ≠ p ∧ c ≠ p ∧ a ≠ 2 ∧ b ≠ 2 ∧
      c ≠ 2 ∧ ¬ a ∣ Q - 1 ∧ ¬ b ∣ Q - 1 ∧ ¬ c ∣ Q - 1 ∧ ¬ a ∣ Q ^ 2 - 1 ∧
      ¬ b ∣ Q ^ 2 - 1 ∧ (3 ≤ Q → ¬ c ∣ Q ^ 2 - 1) := by
  rcases hQ.eq_or_lt with rfl | hQ3
  · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpQ
    subst hp2
    refine ⟨7, 5, 3, ?_⟩
    norm_num
  · have hQ3 : 3 ≤ Q := hQ3
    obtain ⟨a, ha⟩ := exists_ppd hQ3 (show 3 ≤ 3 by norm_num)
    obtain ⟨b, hb⟩ := exists_ppd hQ3 (show 3 ≤ 4 by norm_num)
    obtain ⟨c, hc⟩ := exists_ppd hQ3 (show 3 ≤ 6 by norm_num)
    exact ⟨a, b, c, ha.1, hb.1, hc.1, ha.2.1, hb.2.1, hc.2.1,
      ha.ne hb (by norm_num) (by norm_num), ha.ne hc (by norm_num) (by norm_num),
      hb.ne hc (by norm_num) (by norm_num),
      ha.ne_char (by norm_num) (by omega) hpQ, hb.ne_char (by norm_num) (by omega) hpQ,
      hc.ne_char (by norm_num) (by omega) hpQ,
      ha.ne_two (by norm_num) (by omega), hb.ne_two (by norm_num) (by omega),
      hc.ne_two (by norm_num) (by omega),
      ha.not_dvd_one (by norm_num), hb.not_dvd_one (by norm_num), hc.not_dvd_one (by norm_num),
      ha.not_dvd_sq le_rfl, hb.not_dvd_sq (by norm_num),
      fun _ => hc.not_dvd_sq (by norm_num)⟩

theorem X_minus {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    ∃ x, x.Prime ∧ x ≠ p ∧ x * (Q - 1) ∣ Q ^ 2 - 1 := by
  refine ⟨(Q + 1).minFac, Nat.minFac_prime (by omega), ?_, ?_⟩
  · intro h
    exact not_dvd_add_one hpQ (h ▸ Nat.minFac_dvd _) hp
  · rw [sq_sub_one_eq (by omega), mul_comm (Q - 1)]
    exact mul_dvd_mul_right (Nat.minFac_dvd _) _

theorem X_plus {Q p : ℕ} (hQ : 3 ≤ Q) (hp : p.Prime) (hpQ : p ∣ Q) :
    ∃ x, x.Prime ∧ x ≠ p ∧ x * (Q + 1) ∣ Q ^ 2 - 1 := by
  refine ⟨(Q - 1).minFac, Nat.minFac_prime (by omega), ?_, ?_⟩
  · intro h
    have h1 : p ∣ Q - 1 := h ▸ Nat.minFac_dvd _
    have h2 : p ∣ Q - 1 + 1 := by rwa [Nat.sub_add_cancel (by omega : 1 ≤ Q)]
    exact not_dvd_add_one h1 h2 hp
  · rw [sq_sub_one_eq (by omega)]
    exact mul_dvd_mul_right (Nat.minFac_dvd _) _

end CFSGOutside.HerzogK3Groups.Large
