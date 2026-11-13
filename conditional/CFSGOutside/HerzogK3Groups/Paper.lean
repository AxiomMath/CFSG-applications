import Mathlib
import CFSGOutside.Common.OrderShape
import CFSGOutside.HerzogK3Groups.Large
import CFSGOutside.HerzogK3Groups.A1
import CFSGOutside.HerzogK3Groups.Defs

namespace CFSGOutside.HerzogK3Groups

open CFSGOutside.Corpus CFSGOutside.Corpus.Open
  CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator
  CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.I1420
  CFSGOutside.HerzogK3Groups.Large CFSGOutside.HerzogK3Groups.Small CFSGOutside.HerzogK3Groups.Rest CFSGOutside.HerzogK3Groups.A1

variable [SL2MinimalFaithfulZsigmondy]


theorem pow_char_two {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (h2 : 2 ∣ p ^ e) : p = 2 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)).symm

theorem A1_mem {Q p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (hQ : Q = p ^ e) (h4 : 4 ≤ Q)
    (h3 : (orderA 1 Q).primeFactors.card = 3) : orderA 1 Q ∈ herzogOrders := by
  rw [orderA_one] at h3 ⊢
  rcases Nat.even_or_odd Q with he' | ho
  · have h2 : 2 ∣ Q := even_iff_two_dvd.1 he'
    have hp2 := pow_char_two hp he (hQ ▸ h2)
    have hg : Nat.gcd 2 (Q - 1) = 1 := by
      apply Nat.Coprime.gcd_eq_one
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      obtain ⟨c, hc⟩ := he'
      omega
    rw [hg, Nat.div_one] at h3 ⊢
    rcases A1_even (f := e) (by rw [hQ, hp2]) h4 h3 with rfl | rfl
    · decide +kernel
    · decide +kernel
  · have hg : Nat.gcd 2 (Q - 1) = 2 := by
      apply Nat.gcd_eq_left
      obtain ⟨c, hc⟩ := ho
      exact ⟨c, by omega⟩
    rw [hg] at h3 ⊢
    rcases A1_odd hp he hQ ho (by obtain ⟨c, hc⟩ := ho; omega) h3 with
      rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

theorem A2_mem {Q p : ℕ} (hp : p.Prime) (hpQ : p ∣ Q) (hQ2 : 2 ≤ Q)
    (h3 : (orderA 2 Q).primeFactors.card = 3) : orderA 2 Q ∈ herzogOrders := by
  rcases (by omega : Q = 2 ∨ Q = 3 ∨ 4 ≤ Q) with rfl | rfl | h4
  · decide +kernel
  · decide +kernel
  · exact absurd (four_A2 hp hpQ h4) (by omega)

theorem lie_A (r : ℕ) (q : TauCeti.PrimePower) (hr : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card))
    (h3 : (orderA r q.card).primeFactors.card = 3) : orderA r q.card ∈ herzogOrders := by
  rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | h
  · exact A1_mem q.prime_p q.exponent_pos.ne' (TauCeti.PrimePower.card_def q) (hr.2 rfl) h3
  · exact A2_mem q.prime_p (char_dvd_card q) (card_ge_two q) h3
  · exact absurd (four_A r h q) (by omega)

theorem lie_case (d : TauCeti.LieTypeIndex) (hr : d.InStandardRange)
    (h3 : (lieOrderFormula d).primeFactors.card = 3) : lieOrderFormula d ∈ herzogOrders := by
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
  have h4 : ∀ {N : ℕ}, 4 ≤ N.primeFactors.card → N.primeFactors.card = 3 → N ∈ herzogOrders := fun h h' => by omega
  cases d with
  | A r q => exact lie_A r q hr h3
  | twistedA r q =>
    simp only [lieOrderFormula] at h3 ⊢
    rcases (by omega : r = 2 ∨ r = 3 ∨ 4 ≤ r) with rfl | rfl | h
    · rcases (by have := hr.2 rfl; omega : q.card = 3 ∨ 4 ≤ q.card) with h | h
      · rw [h]; decide +kernel
      · exact h4 (by simpa using four_twistedA2 q.prime_p (char_dvd_card q) h) h3
    · by_cases hq : q.card = 2
      · rw [hq]; decide +kernel
      · exact h4 (four_twistedA 3 le_rfl q (Or.inl (by have := card_ge_two q; omega))) h3
    · exact h4 (four_twistedA r (by omega) q (Or.inr h)) h3
  | B r q =>
    simp only [lieOrderFormula] at h3 ⊢
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | h
    · rcases (by have := card_ge_two q; have := hr.2; omega : q.card = 3 ∨ 4 ≤ q.card) with h | h
      · rw [h]; decide +kernel
      · exact h4 (four_B2 q.prime_p (char_dvd_card q) h) h3
    · exact h4 (four_B r h q) h3
  | C r q =>
    simp only [lieOrderFormula] at h3 ⊢
    exact h4 (four_B r hr.1 q) h3
  | D r q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_D r hr q) h3
  | twistedD r q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_twistedD r hr q) h3
  | E6 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_E6 q) h3
  | E7 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_E7 q) h3
  | E8 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_E8 q) h3
  | F4 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_F4 q) h3
  | G2 q =>
    simp only [lieOrderFormula] at h3 ⊢
    exact h4 (four_G2 q.prime_p (char_dvd_card q) hr) h3
  | twistedE6 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_twistedE6 q) h3
  | trialityD4 q => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_trialityD4 q) h3
  | suzuki m => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_suzuki m hr) h3
  | reeG2 m => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_ree m hr) h3
  | reeF4 m => simp only [lieOrderFormula] at h3 ⊢; exact h4 (four_reeF4 m hr) h3
  | tits => simp only [lieOrderFormula] at h3 ⊢; exact h4 four_tits h3

theorem dvd_half {m p : ℕ} (hp : Nat.Coprime 2 p) (h2 : 2 ∣ m) (h : p ∣ m) : p ∣ m / 2 :=
  Nat.dvd_div_of_mul_dvd (by rw [mul_comm]; exact hp.symm.mul_dvd_of_dvd_of_dvd h h2)

theorem alt_case (n : ℕ) (hn : 5 ≤ n) (h3 : (n.factorial / 2).primeFactors.card = 3) :
    n.factorial / 2 ∈ herzogOrders := by
  rcases (by omega : n = 5 ∨ n = 6 ∨ 7 ≤ n) with rfl | rfl | h
  · decide +kernel
  · decide +kernel
  · exfalso
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h4 : 2 * 2 ∣ n.factorial := by
      have := Nat.dvd_factorial (show 0 < 4 by norm_num) (show 4 ≤ n by omega)
      simpa using this
    have hN : n.factorial / 2 ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) h2) (by norm_num)).ne'
    have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (Nat.dvd_div_of_mul_dvd h4)
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
    omega

theorem spor_false (s : TauCeti.SporadicName) (h3 : (sporOrd s).primeFactors.card = 3) : False := by
  obtain ⟨h2, h3', h5, h7⟩ := CFSGOutside.OrderShape.sporadic_four_primes s
  have hN : sporOrd s ≠ 0 := (CFSGOutside.OrderShape.sporOrd_pos s).ne'
  rcases h7 with h | h | h | h
  · have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 h3' h5 h
    omega
  · have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 h3' h5 h
    omega
  · have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 h3' h5 h
    omega
  · have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) h2 h3' h5 h
    omega

theorem spor_case (s : TauCeti.SporadicName) (h3 : (sporOrd s).primeFactors.card = 3) :
    sporOrd s ∈ herzogOrders := (spor_false s h3).elim

/-- Herzog (1968): a nonabelian finite simple group with exactly three prime divisors has one of
the orders 60, 168, 360, 504, 2448, 5616, 6048, 25920. -/
theorem herzog_orders [CfsgClassification] [LieOrderBridgeHolds] [SporadicOrdersTableHolds]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    Nat.card G ∈ herzogOrders := by
  rcases CFSGOutside.OrderShape.card_shape G hnonab with ⟨s, hs⟩ | ⟨n, hn, hs⟩ | ⟨idx, hs⟩
  · rw [hs] at h3 ⊢; exact spor_case s h3
  · rw [hs] at h3 ⊢; exact alt_case n hn h3
  · rw [hs] at h3 ⊢; exact lie_case idx.1 ((TauCeti.LieTypeIndex.valid_iff _).1 idx.2).1 h3


theorem alt_n (n : ℕ) (hn : 5 ≤ n) (h3 : (n.factorial / 2).primeFactors.card = 3) : n = 5 ∨ n = 6 := by
  rcases (by omega : n = 5 ∨ n = 6 ∨ 7 ≤ n) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h4 : 2 * 2 ∣ n.factorial := by
      have := Nat.dvd_factorial (show 0 < 4 by norm_num) (show 4 ≤ n by omega)
      simpa using this
    have hN : n.factorial / 2 ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) h2) (by norm_num)).ne'
    have := four_nat hN Nat.prime_two Nat.prime_three (by norm_num : Nat.Prime 5)
      (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (Nat.dvd_div_of_mul_dvd h4)
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
      (dvd_half (by norm_num) h2 (Nat.dvd_factorial (by norm_num) (by omega)))
    omega

theorem A1_params {Q p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (hQ : Q = p ^ e) (h4 : 4 ≤ Q)
    (h3 : (orderA 1 Q).primeFactors.card = 3) :
    Q = 4 ∨ Q = 5 ∨ Q = 7 ∨ Q = 8 ∨ Q = 9 ∨ Q = 17 := by
  rw [orderA_one] at h3
  rcases Nat.even_or_odd Q with he' | ho
  · have h2 : 2 ∣ Q := even_iff_two_dvd.1 he'
    have hp2 := pow_char_two hp he (hQ ▸ h2)
    have hg : Nat.gcd 2 (Q - 1) = 1 := by
      apply Nat.Coprime.gcd_eq_one
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      obtain ⟨c, hc⟩ := he'
      omega
    rw [hg, Nat.div_one] at h3
    rcases A1_even (f := e) (by rw [hQ, hp2]) h4 h3 with h | h <;> simp [h]
  · have hg : Nat.gcd 2 (Q - 1) = 2 := by
      apply Nat.gcd_eq_left
      obtain ⟨c, hc⟩ := ho
      exact ⟨c, by omega⟩
    rw [hg] at h3
    rcases A1_odd hp he hQ ho (by obtain ⟨c, hc⟩ := ho; omega) h3 with h | h | h | h <;> simp [h]

theorem lie_params (d : TauCeti.LieTypeIndex) (hr : d.InStandardRange)
    (h3 : (lieOrderFormula d).primeFactors.card = 3) : HerzogLie d := by
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
  have h4 : ∀ {N : ℕ}, 4 ≤ N.primeFactors.card → N.primeFactors.card = 3 → HerzogLie d :=
    fun h h' => absurd h' (by omega)
  cases d with
  | A r q =>
    rcases (by omega : r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | h
    · have := A1_params q.prime_p q.exponent_pos.ne' (TauCeti.PrimePower.card_def q) (hr.2 rfl) h3
      simp only [HerzogLie]; omega
    · rcases (by have := card_ge_two q; omega : q.card = 2 ∨ q.card = 3 ∨ 4 ≤ q.card) with h | h | h
      · simp only [HerzogLie]; omega
      · simp only [HerzogLie]; omega
      · exact h4 (four_A2 q.prime_p (char_dvd_card q) h) h3
    · exact h4 (four_A r h q) h3
  | twistedA r q =>
    simp only [lieOrderFormula] at h3
    rcases (by omega : r = 2 ∨ r = 3 ∨ 4 ≤ r) with rfl | rfl | h
    · rcases (by have := hr.2 rfl; omega : q.card = 3 ∨ 4 ≤ q.card) with h | h
      · simpa [HerzogLie] using h
      · exact h4 (by simpa using four_twistedA2 q.prime_p (char_dvd_card q) h) h3
    · by_cases hq : q.card = 2
      · simpa [HerzogLie] using hq
      · exact h4 (four_twistedA 3 le_rfl q (Or.inl (by have := card_ge_two q; omega))) h3
    · exact h4 (four_twistedA r (by omega) q (Or.inr h)) h3
  | B r q =>
    simp only [lieOrderFormula] at h3
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | h
    · rcases (by have := card_ge_two q; have := hr.2; omega : q.card = 3 ∨ 4 ≤ q.card) with h | h
      · simpa [HerzogLie] using h
      · exact h4 (four_B2 q.prime_p (char_dvd_card q) h) h3
    · exact h4 (four_B r h q) h3
  | C r q => simp only [lieOrderFormula] at h3; exact h4 (four_B r hr.1 q) h3
  | D r q => simp only [lieOrderFormula] at h3; exact h4 (four_D r hr q) h3
  | twistedD r q => simp only [lieOrderFormula] at h3; exact h4 (four_twistedD r hr q) h3
  | E6 q => simp only [lieOrderFormula] at h3; exact h4 (four_E6 q) h3
  | E7 q => simp only [lieOrderFormula] at h3; exact h4 (four_E7 q) h3
  | E8 q => simp only [lieOrderFormula] at h3; exact h4 (four_E8 q) h3
  | F4 q => simp only [lieOrderFormula] at h3; exact h4 (four_F4 q) h3
  | G2 q => simp only [lieOrderFormula] at h3; exact h4 (four_G2 q.prime_p (char_dvd_card q) hr) h3
  | twistedE6 q => simp only [lieOrderFormula] at h3; exact h4 (four_twistedE6 q) h3
  | trialityD4 q => simp only [lieOrderFormula] at h3; exact h4 (four_trialityD4 q) h3
  | suzuki m => simp only [lieOrderFormula] at h3; exact h4 (four_suzuki m hr) h3
  | reeG2 m => simp only [lieOrderFormula] at h3; exact h4 (four_ree m hr) h3
  | reeF4 m => simp only [lieOrderFormula] at h3; exact h4 (four_reeF4 m hr) h3
  | tits => simp only [lieOrderFormula] at h3; exact h4 four_tits h3

/-- Herzog (1968), isomorphism-type form: a nonabelian finite simple group with exactly three prime
divisors is isomorphic to the catalog group at one of the parameter sets in `HerzogCatalog`. -/
theorem herzog_iso [CfsgClassification] [LieOrderBridgeHolds] [SporadicOrdersTableHolds]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    ∃ i : TauCeti.CFSGIndex, HerzogCatalog i ∧ Nonempty (G ≃* i.Group) := by
  obtain ⟨i, ⟨e⟩⟩ := CfsgClassification.cfsg_classification G
  refine ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have hc : Nat.card G = n.factorial / 2 :=
      (Nat.card_congr e.toEquiv).trans (CFSGOutside.OrderShape.card_alternating n hn)
    rw [hc] at h3
    exact alt_n n hn h3
  | lie idx =>
    have hc := LieOrderBridgeHolds.lieOrderBridge_holds idx G ⟨e⟩
    rw [hc] at h3
    exact lie_params idx.1 ((TauCeti.LieTypeIndex.valid_iff _).1 idx.2).1 h3
  | sporadic s =>
    have hc : Nat.card G = sporOrd s := (Nat.card_congr e.toEquiv).trans (SporadicOrdersTableHolds.sporadicOrdersTable_holds s)
    rw [hc] at h3
    exact (spor_false s h3).elim

end CFSGOutside.HerzogK3Groups
