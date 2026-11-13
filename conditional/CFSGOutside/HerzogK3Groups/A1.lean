import Mathlib
import CFSGOutside.HerzogK3Groups.Rest

namespace CFSGOutside.HerzogK3Groups.A1

open CFSGOutside.Corpus.Open CFSGOutside.HerzogK3Groups.Large CFSGOutside.HerzogK3Groups.Small
  CFSGOutside.HerzogK3Groups.Rest Finset

variable [CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy]

theorem orderA_one (Q : ℕ) : orderA 1 Q = Q * (Q ^ 2 - 1) / Nat.gcd 2 (Q - 1) := by
  have : Finset.Icc 2 (1 + 1) = {2} := by decide
  simp only [orderA, this, Finset.prod_singleton]
  all_goals norm_num

theorem four_dvd_two_pow {u : ℕ} (h : 2 ≤ u) : 4 ∣ 2 ^ u := by
  have := Nat.pow_dvd_pow 2 h
  norm_num at this
  exact this

theorem eight_dvd_two_pow {u : ℕ} (h : 3 ≤ u) : 8 ∣ 2 ^ u := by
  have := Nat.pow_dvd_pow 2 h
  norm_num at this
  exact this

theorem sixteen_dvd_two_pow {u : ℕ} (h : 4 ≤ u) : 16 ∣ 2 ^ u := by
  have := Nat.pow_dvd_pow 2 h
  norm_num at this
  exact this

theorem three_pow_mod_sixteen (c : ℕ) : 3 ^ c % 16 = 3 ^ (c % 4) % 16 := by
  conv_lhs => rw [← Nat.div_add_mod c 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_add_one_eq_three_pow {n c : ℕ} (h : 2 ^ n + 1 = 3 ^ c) : n = 1 ∨ n = 3 := by
  by_cases hn : 4 ≤ n
  · exfalso
    have h16 := sixteen_dvd_two_pow hn
    have hc := three_pow_mod_sixteen c
    have hc4 : c % 4 = 0 := by
      have hr : c % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases hr4 : c % 4 <;> simp at hc <;> omega
    have h5 : 5 ∣ 3 ^ c - 1 := by
      have e : 3 ^ c = (3 ^ 4) ^ (c / 4) := by
        rw [← pow_mul]; congr 1; omega
      have := sub_one_dvd (3 ^ 4) (c / 4)
      rw [← e] at this
      exact (by norm_num : 5 ∣ 3 ^ 4 - 1).trans this
    have : 5 ∣ 2 ^ n := by
      have e : 3 ^ c - 1 = 2 ^ n := by rw [← h]; simp
      rwa [e] at h5
    exact absurd ((Nat.Prime.dvd_of_dvd_pow (by norm_num) this)) (by norm_num)
  · push_neg at hn
    interval_cases n
    · exfalso
      rcases c with _ | c
      · simp at h
      · rw [pow_succ] at h; omega
    · left; rfl
    · exfalso
      rcases c with _ | c
      · simp at h
      · rw [pow_succ] at h; omega
    · right; rfl

theorem two_pow_eq_three_pow_add_one {n c : ℕ} (h : 2 ^ n = 3 ^ c + 1) (hn : 2 ≤ n) : n = 2 := by
  by_contra hne
  have h8 := eight_dvd_two_pow (show 3 ≤ n by omega)
  have := three_pow_mod_eight c
  omega

theorem pow_three_eq_nine {k s : ℕ} (hs : 3 ^ k - 1 = 2 ^ s) (h5 : 5 ≤ 3 ^ k) : 3 ^ k = 9 := by
  rcases Nat.even_or_odd k with ⟨g, hg⟩ | ⟨g, hg⟩
  · have ht : 3 ^ k = (3 ^ g) ^ 2 := by
      rw [hg, ← pow_mul]; congr 1; ring
    have hg0 : g ≠ 0 := by
      rintro rfl
      simp at hg
      subst hg
      simp at h5
    have ht3 : 3 ≤ 3 ^ g := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    set t := 3 ^ g with htdef
    have hfac : (t - 1) * (t + 1) = 2 ^ s := by
      rw [← hs, ht]; exact (sq_sub_one_eq (by omega)).symm
    obtain ⟨u, hu, hu'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
    obtain ⟨v, hv, hv'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
    have hu2 : u ≤ 1 := by
      by_contra hcon
      have h1 : 4 ∣ t - 1 := hu' ▸ four_dvd_two_pow (by omega)
      have hv2 : 2 ≤ v := by
        by_contra hv2
        interval_cases v <;> omega
      have h2 : 4 ∣ t + 1 := hv' ▸ four_dvd_two_pow hv2
      omega
    have : t - 1 ≤ 2 := by
      rw [hu']
      calc 2 ^ u ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hu2
        _ = 2 := by norm_num
    have ht3' : t = 3 := by omega
    rw [ht, ht3']
    norm_num
  · exfalso
    have hmod : 3 ^ k % 8 = 3 := by
      rw [hg, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 2 ^ s % 8 = 2 := by omega
    rcases Nat.lt_or_ge s 3 with h | h
    · interval_cases s <;> omega
    · have := eight_dvd_two_pow h
      omega

theorem primeFactors_half {Q : ℕ} (hodd : Odd Q) (h5 : 5 ≤ Q) :
    (Q * (Q ^ 2 - 1) / 2).primeFactors = (Q * (Q ^ 2 - 1)).primeFactors := by
  obtain ⟨c, hc⟩ := hodd
  have hG : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := sq_sub_one_eq (by omega)
  have h4 : 4 ∣ Q ^ 2 - 1 := by
    rw [hG]
    have : (Q - 1) * (Q + 1) = 4 * (c * (c + 1)) := by
      obtain rfl : Q = 2 * c + 1 := hc
      have : 2 * c + 1 - 1 = 2 * c := by omega
      rw [this]; ring
    rw [this]; exact dvd_mul_right _ _
  have hM : Q * (Q ^ 2 - 1) ≠ 0 := mul_ne_zero (by omega) (pow_sub_one_ne (by omega) (by norm_num))
  have hM2 : 2 * 2 ∣ Q * (Q ^ 2 - 1) := (by norm_num : 2 * 2 = 4) ▸ h4.mul_left Q |> fun h => by
    exact (show 4 ∣ Q * (Q ^ 2 - 1) from h4.mul_left Q)
  have hN : Q * (Q ^ 2 - 1) / 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) ((dvd_mul_right 2 2).trans hM2)) (by norm_num)).ne'
  ext ℓ
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hℓ, hd, -⟩
    exact ⟨hℓ, hd.trans (Nat.div_dvd_of_dvd ((dvd_mul_right 2 2).trans hM2)), hM⟩
  · rintro ⟨hℓ, hd, -⟩
    refine ⟨hℓ, ?_, hN⟩
    by_cases h2 : ℓ = 2
    · subst h2
      exact Nat.dvd_div_of_mul_dvd hM2
    · have hcop : Nat.Coprime 2 ℓ :=
        (Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm h2)
      exact Nat.dvd_div_of_mul_dvd (hcop.mul_dvd_of_dvd_of_dvd ((dvd_mul_right 2 2).trans hM2) hd)

theorem all_primes_two_pow {n : ℕ} (h0 : n ≠ 0) (h : ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ = 2) :
    ∃ s, n = 2 ^ s :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd h0 (fun hd hdn => h _ hd hdn)⟩

theorem A1_odd {Q p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hQ : Q = p ^ k) (hodd : Odd Q)
    (h5 : 5 ≤ Q) (h3 : (Q * (Q ^ 2 - 1) / 2).primeFactors.card = 3) :
    Q = 5 ∨ Q = 7 ∨ Q = 9 ∨ Q = 17 := by
  have hG0 : Q ^ 2 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  have hfac : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := sq_sub_one_eq (by omega)
  obtain ⟨c, hc⟩ := hodd
  have h2G : 2 ∣ Q ^ 2 - 1 := by
    rw [hfac]; exact Dvd.dvd.mul_right ⟨c, by omega⟩ _
  have hpQ : p ∣ Q := hQ ▸ dvd_pow_self p hk
  rw [primeFactors_half ⟨c, hc⟩ h5, Nat.primeFactors_mul (by omega) hG0] at h3
  have hQp : Q.primeFactors = {p} := by rw [hQ]; exact Nat.primeFactors_prime_pow hk hp
  have hdisj : Disjoint ({p} : Finset ℕ) (Q ^ 2 - 1).primeFactors := by
    rw [Finset.disjoint_singleton_left, Nat.mem_primeFactors]
    rintro ⟨_, hd, _⟩
    exact not_dvd_sub_one (Nat.one_le_pow _ _ (by omega)) (dvd_pow hpQ (by norm_num)) hd hp
  rw [hQp, Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at h3
  have hT : ((Q ^ 2 - 1).primeFactors).card = 2 := by omega
  obtain ⟨x, y, hxy, hTxy⟩ := Finset.card_eq_two.1 hT
  have hmem : ∀ ℓ, ℓ.Prime → ℓ ∣ Q ^ 2 - 1 → ℓ = x ∨ ℓ = y := by
    intro ℓ hl hd
    have : ℓ ∈ (Q ^ 2 - 1).primeFactors := Nat.mem_primeFactors.2 ⟨hl, hd, hG0⟩
    rw [hTxy] at this
    simpa using this
  have hxT : x ∈ (Q ^ 2 - 1).primeFactors := by rw [hTxy]; simp
  have hyT : y ∈ (Q ^ 2 - 1).primeFactors := by rw [hTxy]; simp
  have h2T : 2 ∈ (Q ^ 2 - 1).primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2G, hG0⟩
  have hx := Nat.mem_primeFactors.1 hxT
  have hy := Nat.mem_primeFactors.1 hyT
  obtain ⟨r, hr, hr2, hrall⟩ : ∃ r, r.Prime ∧ r ≠ 2 ∧ ∀ ℓ, ℓ.Prime → ℓ ∣ Q ^ 2 - 1 →
      ℓ = 2 ∨ ℓ = r := by
    rw [hTxy] at h2T
    rcases (by simpa using h2T : 2 = x ∨ 2 = y) with h | h
    · subst h
      exact ⟨y, hy.1, fun h => hxy h.symm, fun ℓ hl hd => hmem ℓ hl hd⟩
    · subst h
      refine ⟨x, hx.1, hxy, fun ℓ hl hd => (hmem ℓ hl hd).symm⟩
  have hr3 : p ≠ 3 → r = 3 := by
    intro hp3
    have h3Q : ¬ 3 ∣ Q := by
      intro h
      rw [hQ] at h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)).symm
    have : 3 ∣ Q ^ 2 - 1 := by
      rw [hfac]
      have hm : Q % 3 = 1 ∨ Q % 3 = 2 := by
        have := Nat.mod_lt Q (show 0 < 3 by norm_num)
        have h0 : Q % 3 ≠ 0 := fun h => h3Q (Nat.dvd_of_mod_eq_zero h)
        omega
      rcases hm with h | h
      · exact (Nat.dvd_of_mod_eq_zero (by omega : (Q - 1) % 3 = 0)).mul_right _
      · exact (Nat.dvd_of_mod_eq_zero (by omega : (Q + 1) % 3 = 0)).mul_left _
    rcases hrall 3 Nat.prime_three this with h | h
    · omega
    · exact h.symm
  have hQ1 : Q - 1 ∣ Q ^ 2 - 1 := sub_one_dvd Q 2
  have hQ2 : Q + 1 ∣ Q ^ 2 - 1 := add_one_dvd_sq (by omega)
  by_cases hrQ : r ∣ Q - 1
  · -- Q + 1 is a power of two
    obtain ⟨s, hs⟩ : ∃ s, Q + 1 = 2 ^ s := by
      refine all_primes_two_pow (by omega) ?_
      intro ℓ hl hd
      rcases hrall ℓ hl (hd.trans hQ2) with h | h
      · exact h
      · subst h
        have h1 : ℓ ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub hd hrQ
        rw [show Q + 1 - (Q - 1) = 2 by omega] at h1
        exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h1) hr2
    have hs3 : 3 ≤ s := by
      by_contra hcon
      interval_cases s <;> omega
    by_cases hp3 : p = 3
    · exfalso
      subst hp3
      have h8 := eight_dvd_two_pow hs3
      have := three_pow_mod_eight k
      rw [← hQ] at this
      omega
    · have hr3' := hr3 hp3
      subst hr3'
      obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      obtain ⟨cc, hcc⟩ : ∃ cc, 2 ^ n - 1 = 3 ^ cc := by
        refine ⟨(2 ^ n - 1).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd (by
          have : 2 ≤ n := by omega
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
          norm_num at this; omega) ?_⟩
        intro ℓ hl hd
        have hd' : ℓ ∣ Q - 1 := by
          have e : Q - 1 = 2 * (2 ^ n - 1) := by
            rw [pow_succ] at hs
            omega
          rw [e]; exact hd.mul_left _
        rcases hrall ℓ hl (hd'.trans hQ1) with h | h
        · subst h
          exfalso
          have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
          omega
        · exact h
      have hn2 : n = 2 := by
        refine two_pow_eq_three_pow_add_one (c := cc) ?_ (by omega)
        have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        omega
      subst hn2
      right; left
      norm_num at hs; omega
  · -- Q - 1 is a power of two
    obtain ⟨s, hs⟩ : ∃ s, Q - 1 = 2 ^ s := by
      refine all_primes_two_pow (by omega) ?_
      intro ℓ hl hd
      rcases hrall ℓ hl (hd.trans hQ1) with h | h
      · exact h
      · subst h; exact absurd hd hrQ
    have hs2 : 2 ≤ s := by
      by_contra hcon
      interval_cases s <;> omega
    by_cases hp3 : p = 3
    · subst hp3
      have : 3 ^ k = 9 := pow_three_eq_nine (by rw [← hQ]; exact hs) (by rw [← hQ]; exact h5)
      right; right; left
      rw [hQ]; exact this
    · have hr3' := hr3 hp3
      subst hr3'
      obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
      obtain ⟨cc, hcc⟩ : ∃ cc, 2 ^ n + 1 = 3 ^ cc := by
        refine ⟨(2 ^ n + 1).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
        intro ℓ hl hd
        have hd' : ℓ ∣ Q + 1 := by
          have e : Q + 1 = 2 * (2 ^ n + 1) := by
            rw [pow_succ] at hs
            omega
          rw [e]; exact hd.mul_left _
        rcases hrall ℓ hl (hd'.trans hQ2) with h | h
        · subst h
          exfalso
          have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
          omega
        · exact h
      rcases two_pow_add_one_eq_three_pow hcc with h | h
      · subst h
        left
        norm_num at hs; omega
      · subst h
        right; right; right
        norm_num at hs; omega

theorem A1_even {Q f : ℕ} (hQ : Q = 2 ^ f) (h4 : 4 ≤ Q)
    (h3 : (Q * (Q ^ 2 - 1)).primeFactors.card = 3) : Q = 4 ∨ Q = 8 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hQ
    omega
  have h2Q : 2 ∣ Q := hQ ▸ dvd_pow_self 2 hf
  obtain ⟨c, hc⟩ := h2Q
  have hfac : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := sq_sub_one_eq (by omega)
  have hG0 : Q ^ 2 - 1 ≠ 0 := pow_sub_one_ne (by omega) (by norm_num)
  rw [Nat.primeFactors_mul (by omega) hG0, hfac,
    Nat.primeFactors_mul (by omega) (by omega)] at h3
  have hQp : Q.primeFactors = {2} := by rw [hQ]; exact Nat.primeFactors_prime_pow hf Nat.prime_two
  have hd1 : Disjoint (Q - 1).primeFactors (Q + 1).primeFactors := by
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    rw [Nat.mem_primeFactors] at h1 h2
    have h5 : ℓ ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub h2.2.1 h1.2.1
    rw [show Q + 1 - (Q - 1) = 2 by omega] at h5
    have := (Nat.prime_dvd_prime_iff_eq h1.1 Nat.prime_two).1 h5
    subst this
    omega
  have hd2 : Disjoint ({2} : Finset ℕ) ((Q - 1).primeFactors ∪ (Q + 1).primeFactors) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_union, Nat.mem_primeFactors,
      Nat.mem_primeFactors]
    rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega
  rw [hQp, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_singleton] at h3
  have ha : 0 < (Q - 1).primeFactors.card :=
    Finset.card_pos.2 ⟨(Q - 1).minFac, Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega),
      Nat.minFac_dvd _, by omega⟩⟩
  have hb : 0 < (Q + 1).primeFactors.card :=
    Finset.card_pos.2 ⟨(Q + 1).minFac, Nat.mem_primeFactors.2 ⟨Nat.minFac_prime (by omega),
      Nat.minFac_dvd _, by omega⟩⟩
  have ha1 : (Q - 1).primeFactors.card = 1 := by omega
  have hb1 : (Q + 1).primeFactors.card = 1 := by omega
  have h3Q : ¬ 3 ∣ Q := by
    intro h
    rw [hQ] at h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hm : Q % 3 = 1 ∨ Q % 3 = 2 := by
    have := Nat.mod_lt Q (show 0 < 3 by norm_num)
    have h0 : Q % 3 ≠ 0 := fun h => h3Q (Nat.dvd_of_mod_eq_zero h)
    omega
  rcases hm with hm | hm
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.1 ha1
    have h3m : 3 ∈ (Q - 1).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.prime_three, Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
    rw [hr, Finset.mem_singleton] at h3m
    subst h3m
    obtain ⟨a, ha'⟩ : ∃ a, Q - 1 = 3 ^ a :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {d} hd hdn => by
        have : d ∈ (Q - 1).primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, by omega⟩
        rw [hr] at this
        simpa using this)⟩
    left
    have := two_pow_eq_three_pow_add_one (n := f) (c := a) (by rw [← hQ]; omega) (by
      by_contra hcon
      interval_cases f <;> omega)
    subst this
    omega
  · obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hb1
    have h3m : 3 ∈ (Q + 1).primeFactors :=
      Nat.mem_primeFactors.2 ⟨Nat.prime_three, Nat.dvd_of_mod_eq_zero (by omega), by omega⟩
    rw [hr, Finset.mem_singleton] at h3m
    subst h3m
    obtain ⟨b, hb'⟩ : ∃ b, Q + 1 = 3 ^ b :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {d} hd hdn => by
        have : d ∈ (Q + 1).primeFactors := Nat.mem_primeFactors.2 ⟨hd, hdn, by omega⟩
        rw [hr] at this
        simpa using this)⟩
    right
    rcases two_pow_add_one_eq_three_pow (n := f) (c := b) (by rw [← hQ]; omega) with h | h
    · subst h; omega
    · subst h; omega

end CFSGOutside.HerzogK3Groups.A1
