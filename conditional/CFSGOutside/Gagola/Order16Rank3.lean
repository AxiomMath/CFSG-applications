import CFSGOutside.Corpus.Gh74SectionalTwoRankFour
import CFSGOutside.Gagola.TwoPrimes

/-!
# Simple groups with Sylow 2-subgroups of order 16 and 2-rank at least 3

Using the Gorenstein-Harada classification of simple groups of sectional 2-rank at most 4 (the class
`Gh74SectionalTwoRankFour`), a finite nonabelian simple group with Sylow 2-subgroups of order `16` and
`2`-rank `≥ 3` has order `4080 = 2^4 * 3 * 5 * 17`, so its Sylow `3`- and `5`-subgroups are cyclic of prime order.
-/

namespace CFSGOutside.Gagola

open CFSGOutside.Corpus CFSGOutside.Corpus.Open

section Generation

/-- Greedy generation: a subgroup of order at most `2 ^ k * |closure t|` containing `closure t` is generated
by `|t| + k` elements. -/
theorem exists_closure_of_card_le {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    ∀ (k : ℕ) (t : Finset G), Subgroup.closure (t : Set G) ≤ P →
      Nat.card P ≤ 2 ^ k * Nat.card (Subgroup.closure (t : Set G)) →
      ∃ s : Finset G, s.card ≤ t.card + k ∧ Subgroup.closure (s : Set G) = P := by
  classical
  intro k
  induction k with
  | zero =>
    intro t hle hcard
    exact ⟨t, by simp, Subgroup.eq_of_le_of_card_ge hle (by simpa using hcard)⟩
  | succ k ih =>
    intro t hle hcard
    by_cases hP : Subgroup.closure (t : Set G) = P
    · exact ⟨t, by omega, hP⟩
    · have hlt : Subgroup.closure (t : Set G) < P := lt_of_le_of_ne hle hP
      obtain ⟨x, hxP, hxt⟩ := SetLike.exists_of_lt hlt
      have hxt' : x ∉ Subgroup.closure (t : Set G) := hxt
      have hle' : Subgroup.closure ((insert x t : Finset G) : Set G) ≤ P := by
        rw [Subgroup.closure_le]
        intro y hy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hy
        rcases hy with rfl | hy
        · exact hxP
        · exact hle (Subgroup.subset_closure hy)
      have h1 : Subgroup.closure (t : Set G) ≤ Subgroup.closure ((insert x t : Finset G) : Set G) :=
        Subgroup.closure_mono (by simp)
      have hxin : x ∈ Subgroup.closure ((insert x t : Finset G) : Set G) :=
        Subgroup.subset_closure (by simp)
      have hne : Subgroup.closure (t : Set G) ≠ Subgroup.closure ((insert x t : Finset G) : Set G) :=
        fun h => hxt' (h ▸ hxin)
      have hdvd := Subgroup.card_dvd_of_le h1
      have hpos : 0 < Nat.card (Subgroup.closure (t : Set G)) := Nat.card_pos
      have hpos' : 0 < Nat.card (Subgroup.closure ((insert x t : Finset G) : Set G)) := Nat.card_pos
      have hneq : Nat.card (Subgroup.closure (t : Set G)) ≠
          Nat.card (Subgroup.closure ((insert x t : Finset G) : Set G)) := by
        intro h
        exact hne (Subgroup.eq_of_le_of_card_ge h1 (le_of_eq h.symm))
      obtain ⟨c, hc⟩ := hdvd
      have hc2 : 2 ≤ c := by
        rcases c with _ | _ | c
        · rw [hc] at hpos'; simp at hpos'
        · exact absurd (by rw [hc]; ring) hneq
        · omega
      have hge : 2 * Nat.card (Subgroup.closure (t : Set G)) ≤
          Nat.card (Subgroup.closure ((insert x t : Finset G) : Set G)) := by
        rw [hc]; nlinarith
      obtain ⟨s, hs, hsP⟩ := ih (insert x t) hle' (by
        calc Nat.card P ≤ 2 ^ (k + 1) * Nat.card (Subgroup.closure (t : Set G)) := hcard
          _ = 2 ^ k * (2 * Nat.card (Subgroup.closure (t : Set G))) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ hge)
      exact ⟨s, le_trans hs (by have := Finset.card_insert_le x t; omega), hsP⟩

theorem exists_closure_of_card_le_two_pow {G : Type*} [Group G] [Finite G] (P : Subgroup G) (k : ℕ)
    (h : Nat.card P ≤ 2 ^ k) : ∃ s : Finset G, s.card ≤ k ∧ Subgroup.closure (s : Set G) = P := by
  obtain ⟨s, hs, hsP⟩ := exists_closure_of_card_le P k ∅ (by simp) (by simpa using h)
  exact ⟨s, by simpa using hs, hsP⟩

end Generation

section Numbers

theorem fac_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fac_two_ne {N a m : ℕ} (hN : N = 2 ^ a * m) (hm : Odd m) (ha : a ≠ 4) :
    N.factorization 2 ≠ 4 := by
  rw [hN, fac_pow_mul Nat.prime_two (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h))
    hm.pos.ne']
  exact ha

theorem fac_two_ne_of_dvd {N : ℕ} (h : 32 ∣ N) : N.factorization 2 ≠ 4 := by
  intro hv
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hv
  have := (Nat.prime_two.pow_dvd_iff_le_factorization hN0).mp (show 2 ^ 5 ∣ N by norm_num; exact h)
  omega

theorem sq_odd_mod8 {q : ℕ} (hq : q % 2 = 1) : q ^ 2 % 8 = 1 := by
  have h : ∀ r < 8, r % 2 = 1 → r ^ 2 % 8 = 1 := by decide
  rw [Nat.pow_mod]
  exact h _ (Nat.mod_lt _ (by norm_num)) (by omega)

theorem pow4_odd_mod16 {q : ℕ} (hq : q % 2 = 1) : q ^ 4 % 16 = 1 := by
  have h : ∀ r < 16, r % 2 = 1 → r ^ 4 % 16 = 1 := by decide
  rw [Nat.pow_mod]
  exact h _ (Nat.mod_lt _ (by norm_num)) (by omega)

theorem eight_dvd_sq {q : ℕ} (hq : q % 2 = 1) : 8 ∣ q ^ 2 - 1 := by
  have h := sq_odd_mod8 hq
  omega

theorem eight_dvd_pow_even {q : ℕ} (hq : q % 2 = 1) {j : ℕ} (hj : 1 ≤ j) : 8 ∣ q ^ (2 * j) - 1 := by
  have h : q ^ (2 * j) % 8 = 1 := by
    rw [pow_mul, Nat.pow_mod, sq_odd_mod8 hq]; simp
  have : 1 ≤ q ^ (2 * j) := Nat.one_le_pow _ _ (by omega)
  omega

theorem sixteen_dvd_q4 {q : ℕ} (hq : q % 2 = 1) : 16 ∣ q ^ 4 - 1 := by
  have h := pow4_odd_mod16 hq
  omega

theorem toNat_even {q i : ℕ} (hi : Even i) (hq : 1 ≤ q) : ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow, ← Nat.cast_pow]
  have := Nat.one_le_pow i q hq
  omega

theorem toNat_odd {q i : ℕ} (hi : Odd i) : ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, ← Nat.cast_pow]
  omega

theorem fac_ne_of_div {M g K : ℕ} (hM : 32 ∣ M) (hg : Nat.Coprime 2 g) (hgM : g ∣ M)
    (hK : K = M / g) : K.factorization 2 ≠ 4 := by
  obtain ⟨c, hc⟩ := hgM
  have hg0 : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hg)
  have : K = c := by rw [hK, hc]; exact Nat.mul_div_cancel_left c hg0
  subst this
  apply fac_two_ne_of_dvd
  rw [hc] at hM
  exact (Nat.Coprime.pow_left 5 hg).dvd_of_dvd_mul_left (by simpa using hM)

end Numbers

section Families

theorem fac_ne_div_four {M g K : ℕ} (hM : 128 ∣ M) (hg : g ∣ 4) (hK : K = M / g) :
    K.factorization 2 ≠ 4 := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg (by norm_num)
  have hg4 : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg
  obtain ⟨c, rfl⟩ := hM
  apply fac_two_ne_of_dvd
  rw [hK]
  interval_cases g <;> first | omega | (exfalso; revert hg; decide)

theorem fac_ordG2 {q : ℕ} (hq : q % 2 = 1) : (ordG2 q).factorization 2 ≠ 4 := by
  apply fac_two_ne_of_dvd
  unfold ordG2
  obtain ⟨a, ha⟩ := eight_dvd_pow_even hq (j := 3) (by norm_num)
  obtain ⟨b, hb⟩ := eight_dvd_sq hq
  rw [show 2 * 3 = 6 from rfl] at ha
  rw [ha, hb]
  exact Dvd.intro (q ^ 6 * a * b * 2) (by ring)

theorem fac_ordTrialityD4 {q : ℕ} (hq : q % 2 = 1) : (ordTrialityD4 q).factorization 2 ≠ 4 := by
  apply fac_two_ne_of_dvd
  unfold ordTrialityD4
  obtain ⟨a, ha⟩ := eight_dvd_pow_even hq (j := 3) (by norm_num)
  obtain ⟨b, hb⟩ := eight_dvd_sq hq
  rw [show 2 * 3 = 6 from rfl] at ha
  rw [ha, hb]
  exact Dvd.intro (q ^ 12 * (q ^ 8 + q ^ 4 + 1) * a * b * 2) (by ring)

theorem fac_ordBC {q : ℕ} (hq : q % 2 = 1) : (ordBC 2 q).factorization 2 ≠ 4 := by
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have e : ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) := by
    unfold ordBC
    rw [hI, Finset.prod_pair (by decide)]
  obtain ⟨a, ha⟩ := eight_dvd_sq hq
  obtain ⟨b, hb⟩ := sixteen_dvd_q4 hq
  refine fac_ne_div_four (M := q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ?_
    (dvd_trans (Nat.gcd_dvd_left _ _) (by norm_num)) e
  rw [ha, hb]
  exact Dvd.intro (q ^ 4 * a * b) (by ring)

theorem fac_ordA3 {q : ℕ} (hq : q % 2 = 1) : (ordA 3 q).factorization 2 ≠ 4 := by
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  have e : ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q - 1) := by
    unfold ordA
    rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  obtain ⟨a, ha⟩ := eight_dvd_sq hq
  obtain ⟨b, hb⟩ := sixteen_dvd_q4 hq
  refine fac_ne_div_four (M := q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)))) ?_
    (Nat.gcd_dvd_left _ _) e
  rw [ha, hb]
  exact Dvd.intro (q ^ 6 * a * (q ^ 3 - 1) * b) (by ring)

theorem fac_ordTwistedA3 {q : ℕ} (hq : q % 2 = 1) (hq1 : 1 ≤ q) :
    (ordTwistedA 3 q).factorization 2 ≠ 4 := by
  have hI : Finset.Icc 2 4 = {2, 3, 4} := by decide
  have e : ordTwistedA 3 q =
      q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q + 1) := by
    unfold ordTwistedA
    rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide),
      toNat_even (by decide) hq1, toNat_odd (by decide), toNat_even (by decide) hq1]
  obtain ⟨a, ha⟩ := eight_dvd_sq hq
  obtain ⟨b, hb⟩ := sixteen_dvd_q4 hq
  refine fac_ne_div_four (M := q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)))) ?_
    (Nat.gcd_dvd_left _ _) e
  rw [ha, hb]
  exact Dvd.intro (q ^ 6 * a * (q ^ 3 + 1) * b) (by ring)

theorem fac_ordA4 {q : ℕ} (hq : q % 2 = 1) : (ordA 4 q).factorization 2 ≠ 4 := by
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  have e : ordA 4 q =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) / Nat.gcd 5 (q - 1) := by
    unfold ordA
    rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  have hg : Nat.gcd 5 (q - 1) ∣ q ^ 5 - 1 :=
    dvd_trans (Nat.gcd_dvd_right _ _) (Nat.sub_one_dvd_pow_sub_one q 5)
  have hg' : Nat.gcd 5 (q - 1) ∣ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hg _) _) _) _
  obtain ⟨a, ha⟩ := eight_dvd_sq hq
  obtain ⟨b, hb⟩ := sixteen_dvd_q4 hq
  refine fac_ne_of_div (M := q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))))
    ?_ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)) hg' e
  rw [ha, hb]
  exact Dvd.intro (4 * (q ^ 10 * a * (q ^ 3 - 1) * b * (q ^ 5 - 1))) (by ring)

theorem fac_ordTwistedA4 {q : ℕ} (hq : q % 2 = 1) (hq1 : 1 ≤ q) :
    (ordTwistedA 4 q).factorization 2 ≠ 4 := by
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  have e : ordTwistedA 4 q =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) / Nat.gcd 5 (q + 1) := by
    unfold ordTwistedA
    rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
      toNat_even (by decide) hq1, toNat_odd (by decide), toNat_even (by decide) hq1,
      toNat_odd (by decide)]
  have hg : Nat.gcd 5 (q + 1) ∣ q ^ 5 + 1 :=
    dvd_trans (Nat.gcd_dvd_right _ _) (by simpa using Odd.nat_add_dvd_pow_add_pow q 1 (n := 5) (by decide))
  have hg' : Nat.gcd 5 (q + 1) ∣ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hg _) _) _) _
  obtain ⟨a, ha⟩ := eight_dvd_sq hq
  obtain ⟨b, hb⟩ := sixteen_dvd_q4 hq
  refine fac_ne_of_div (M := q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))))
    ?_ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)) hg' e
  rw [ha, hb]
  exact Dvd.intro (4 * (q ^ 10 * a * (q ^ 3 + 1) * b * (q ^ 5 + 1))) (by ring)

end Families

section Main

theorem fac_two_pow_mul {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k :=
  fac_pow_mul Nat.prime_two (fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)) hm.pos.ne'

theorem three_pow_odd_mod_eight' (a : ℕ) : 3 ^ (2 * a + 1) % 8 = 3 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem fac_ordRee (a : ℕ) : (ordRee (3 ^ (2 * a + 1))).factorization 2 = 3 := by
  unfold ordRee
  obtain ⟨q, hq⟩ : ∃ q, q = 3 ^ (2 * a + 1) := ⟨_, rfl⟩
  rw [← hq]
  have hq8 : q % 8 = 3 := hq ▸ three_pow_odd_mod_eight' a
  have hA8 : q ^ 3 % 8 = 3 := by rw [Nat.pow_mod, hq8]
  obtain ⟨A, hA⟩ : ∃ A, A = q ^ 3 := ⟨_, rfl⟩
  rw [← hA] at hA8 ⊢
  have e1 : A + 1 = 4 * ((A + 1) / 4) := by omega
  have e2 : q - 1 = 2 * ((q - 1) / 2) := by omega
  rw [e1, e2, show A * (4 * ((A + 1) / 4)) * (2 * ((q - 1) / 2)) =
    2 ^ 3 * (A * ((A + 1) / 4) * ((q - 1) / 2)) by ring]
  refine fac_two_pow_mul ((Odd.mul ?_ ?_).mul ?_) <;> exact Nat.odd_iff.mpr (by omega)

/-- A member of the Gorenstein-Harada list whose 2-part is `16` is `PSL(2, 16)`. -/
theorem eq_4080_of_mem {N : ℕ} (hmem : N ∈ gorensteinHarada74Orders) (hv : N.factorization 2 = 4) :
    N = 4080 := by
  have e8 : ordA 1 8 = 504 := by decide
  have e16 : ordA 1 16 = 4080 := by decide
  have e4 : ordA 2 4 = 20160 := by decide
  have eS : ordSuzuki 8 = 29120 := by unfold ordSuzuki; norm_num
  unfold gorensteinHarada74Orders at hmem
  rcases hmem with ((((h | h) | h) | h) | h)
  · obtain ⟨p, f, hp, hp2, hf, hc⟩ := h
    have hq : (p ^ f) % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · exact absurd h2 hp2
      · rw [Nat.pow_mod, h2]; simp
    have hq1 : 1 ≤ p ^ f := by omega
    exfalso
    rcases hc with h | h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> subst h
    · exact fac_ordG2 hq hv
    · exact fac_ordTrialityD4 hq hv
    · exact fac_ordBC hq hv
    · exact fac_ordA3 hq hv
    · exact fac_ordTwistedA3 hq hq1 hv
    · exact fac_ordA4 hq hv
    · exact fac_ordTwistedA4 hq hq1 hv
  · obtain ⟨k, -, rfl⟩ := h
    rw [fac_ordRee] at hv
    omega
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact absurd hv (fac_two_ne (a := 3) (m := 63) (by rw [e8]; norm_num) (by decide) (by norm_num))
    · exact e16
    · exact absurd hv (fac_two_ne (a := 6) (m := 315) (by rw [e4]; norm_num) (by decide) (by norm_num))
    · exact absurd hv (fac_two_ne (a := 6) (m := 455) (by rw [eS]; norm_num) (by decide) (by norm_num))
  · obtain ⟨n, h8, h11, rfl⟩ := h
    exfalso
    interval_cases n
    · exact fac_two_ne (a := 6) (m := 315) (by norm_num [Nat.factorial]) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 6) (m := 2835) (by norm_num [Nat.factorial]) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 14175) (by norm_num [Nat.factorial]) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 155925) (by norm_num [Nat.factorial]) (by decide) (by norm_num) hv
  · exfalso
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fac_two_ne (a := 6) (m := 3 ^ 3 * 5 * 11) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 3 ^ 2 * 5 * 7 * 11) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 3 ^ 2 * 5 * 7 * 11 * 23) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 3) (m := 3 * 5 * 7 * 11 * 19) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 3 ^ 3 * 5 ^ 2 * 7) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 3 ^ 5 * 5 * 17 * 19) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 7) (m := 3 ^ 6 * 5 ^ 3 * 7 * 11) (by norm_num) (by decide) (by norm_num) hv
    · exact fac_two_ne (a := 8) (m := 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67) (by norm_num) (by decide)
        (by norm_num) hv

theorem sylow16_rank3 [Gh74SectionalTwoRankFour] {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (S : Sylow 2 X) (hS : Nat.card S = 16)
    (hrank : 3 ≤ CFSGOutside.Corpus.Open.twoRank X) : TwoCyclicPrimes X := by
  have hv : (Nat.card X).factorization 2 = 4 := by
    have h := Sylow.card_eq_multiplicity S
    rw [hS] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : (16 : ℕ) = 2 ^ 4)))
  have hsect : ∀ P : Subgroup X, IsPGroup 2 P →
      ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = P := by
    intro P hP
    obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hP
    have hQ : Nat.card Q = 2 ^ 4 := by rw [Sylow.card_eq_multiplicity Q, hv]
    exact exists_closure_of_card_le_two_pow P 4 (hQ ▸ Subgroup.card_le_of_le hPQ)
  have hN : Nat.card X = 4080 :=
    eq_4080_of_mem (Gh74SectionalTwoRankFour.cl_lit_gh74_sectional_two_rank_four X hnonab hrank hsect) hv
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : (Nat.card X).factorization 3 = 1 := by
    rw [hN, show (4080 : ℕ) = 3 ^ 1 * 1360 by norm_num]
    exact fac_pow_mul (by norm_num) (by norm_num) (by norm_num)
  have h5 : (Nat.card X).factorization 5 = 1 := by
    rw [hN, show (4080 : ℕ) = 5 ^ 1 * 816 by norm_num]
    exact fac_pow_mul (by norm_num) (by norm_num) (by norm_num)
  refine ⟨3, 5, inferInstance, inferInstance, by norm_num, ?_, ?_⟩
  · intro P
    have hc : Nat.card P = 3 := by rw [Sylow.card_eq_multiplicity P, h3]; simp
    exact ⟨isCyclic_of_prime_card hc, by omega⟩
  · intro P
    have hc : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity P, h5]; simp
    exact ⟨isCyclic_of_prime_card hc, by omega⟩

end Main

end CFSGOutside.Gagola
