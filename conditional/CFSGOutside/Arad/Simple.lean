import CFSGOutside.Arad.PSL2
import CFSGOutside.Arad.Basic
import CFSGOutside.Corpus.WalterStructure
import CFSGOutside.Corpus.J2Inverted
import CFSGOutside.Corpus.WardLocal
import CFSGOutside.Corpus.GorensteinWalter

/-!
# Arad, Theorem B(iii): the simple groups

No nonabelian simple group with dihedral or abelian Sylow `2`-subgroups is π-homogeneous for a set `π` of odd
primes meeting its order (Arad 1974, proof of Theorem B(iii), p. 7). By Walter's theorem and the
Gorenstein–Walter theorem such a group is `PSL(2, q)`, `A₇`, `J₁` or of Ree type; each case gives a witness
`Bad` against `HomP`:

* `PSL(2, q)`: `modelBad_psl`;
* `A₇`: explicit permutations;
* `J₁`: every odd Sylow subgroup is inverted by an involution (corpus, `J2_inverted`);
* Ree type: the Sylow `3`-normalizer, the Hall subgroups `M±` (corpus, Ward) and `PSL(2, q) ≤ C(J)`.
-/

open scoped MatrixGroups Pointwise

namespace CFSGOutside.Arad

open Subgroup

section General

variable {G : Type*} [Group G]

theorem ModelBad.of_mulEquiv {M : Type*} [Group M] (e : G ≃* M) (h : ModelBad M) : ModelBad G := by
  intro π h2 p hp hpπ hpd
  obtain ⟨r, s, hr, hrπ, hs, hsπ, hb⟩ := h π h2 p hp hpπ (Nat.card_congr e.toEquiv ▸ hpd)
  exact ⟨r, s, hr, hrπ, hs, hsπ, hb.of_mulEquiv e⟩

/-- An `s`-element `g` with `g x g⁻¹ = x ^ m` and `g x ≠ x g`, for `x` of prime order `r`, is a witness
`Bad G r s`. -/
theorem bad_of_conj [Finite G] {r s k m : ℕ} [Fact r.Prime] {x g : G} (hx : orderOf x = r)
    (hgx : g * x * g⁻¹ = x ^ m) (hc : g * x ≠ x * g) (hg : g ^ (s ^ k) = 1) : Bad G r s := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact (Fact.out : r.Prime).ne_one hx.symm
  have hle : MulAut.conj g • zpowers x ≤ zpowers x := by
    intro y hy
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hy
    have : y = g * x ^ i * g⁻¹ := by
      rw [hi]; simp [MulAut.smul_def, mul_assoc]
    rw [this, show g * x ^ i * g⁻¹ = (g * x * g⁻¹) ^ i by simp [conj_zpow], hgx]
    exact zpow_mem (pow_mem (mem_zpowers x) m) i
  have heq : MulAut.conj g • zpowers x = zpowers x :=
    eq_of_le_of_card_ge hle (le_of_eq (Nat.card_congr
      (Subgroup.equivSMul (MulAut.conj g) (zpowers x)).toEquiv))
  refine ⟨zpowers x, ?_, ?_, g, ?_, ?_, k, hg⟩
  · rwa [Ne, zpowers_eq_bot]
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  · rw [mem_normalizer_iff]
    intro y
    have key : g * y * g⁻¹ ∈ zpowers x ↔ y ∈ zpowers x := by
      conv_lhs => rw [← heq]
      rw [mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, mul_assoc]
    exact key.symm
  · intro hgc
    exact hc ((mem_centralizer_iff.mp hgc) x (mem_zpowers x)).symm

end General

section J1

/-- `J₁` is not π-homogeneous (Arad 1974, p. 7, from Janko 1966). -/
theorem modelBad_J1 [CFSGOutside.Corpus.J2Inverted] : ModelBad CFSGOutside.Corpus.Open.walterJ1 := by
  intro π h2 p hp hpπ hpd
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => h2 (h ▸ hpπ)
  obtain ⟨P⟩ : Nonempty (Sylow p CFSGOutside.Corpus.Open.walterJ1) := inferInstance
  obtain ⟨x, hx, hinv⟩ := CFSGOutside.Corpus.J2Inverted.J2_inverted hp2 P
  refine ⟨p, 2, hp, hpπ, Nat.prime_two, h2, bad_of_inverts hp2 (P.ne_bot_of_dvd_card hpd)
    P.isPGroup' (hx ▸ pow_orderOf_eq_one x) hinv⟩

end J1

section A7

open Equiv

/-- `A₇` is not π-homogeneous (Arad 1974, p. 7, via Corollary A). -/
theorem modelBad_A7 : ModelBad (alternatingGroup (Fin 7)) := by
  intro π h2 p hp hpπ hpd
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin,
    show Nat.factorial 7 / 2 = 2520 by decide] at hpd
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    have : p ∣ 2 ^ 3 * (3 ^ 2 * (5 * 7)) := by norm_num; exact hpd
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h) ▸ hpπ) h2
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  let x3 : alternatingGroup (Fin 7) := ⟨[0, 1, 2].formPerm,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  let g3 : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 3 4,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
  have bad3 : Bad (alternatingGroup (Fin 7)) 3 2 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact bad_of_conj (x := x3) (g := g3) (m := 2) (k := 1)
      (orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
        have := congrArg Subtype.val h; revert this; decide +kernel))
      (Subtype.ext (by decide +kernel)) (fun h => by
        have := congrArg Subtype.val h; revert this; decide +kernel) (Subtype.ext (by decide +kernel))
  rcases hp357 with rfl | rfl | rfl
  · exact ⟨3, 2, Nat.prime_three, hpπ, Nat.prime_two, h2, bad3⟩
  · let x5 : alternatingGroup (Fin 7) := ⟨[0, 1, 2, 3, 4].formPerm,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
    let g5 : alternatingGroup (Fin 7) := ⟨swap 1 4 * swap 2 3,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact ⟨5, 2, by norm_num, hpπ, Nat.prime_two, h2,
      bad_of_conj (x := x5) (g := g5) (m := 4) (k := 1)
        (orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
          have := congrArg Subtype.val h; revert this; decide +kernel))
        (Subtype.ext (by decide +kernel)) (fun h => by
          have := congrArg Subtype.val h; revert this; decide +kernel) (Subtype.ext (by decide +kernel))⟩
  · by_cases h3 : 3 ∈ π
    · exact ⟨3, 2, Nat.prime_three, h3, Nat.prime_two, h2, bad3⟩
    · let x7 : alternatingGroup (Fin 7) := ⟨[0, 1, 2, 3, 4, 5, 6].formPerm,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
      let g7 : alternatingGroup (Fin 7) := ⟨[1, 2, 4].formPerm * [3, 6, 5].formPerm,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      exact ⟨7, 3, by norm_num, hpπ, Nat.prime_three, h3,
        bad_of_conj (x := x7) (g := g7) (m := 2) (k := 1)
          (orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
            have := congrArg Subtype.val h; revert this; decide +kernel))
          (Subtype.ext (by decide +kernel)) (fun h => by
            have := congrArg Subtype.val h; revert this; decide +kernel) (Subtype.ext (by decide +kernel))⟩

end A7

section PSL

theorem modelBad_psl_galois (p f : ℕ) [Fact p.Prime] (hf : 4 ≤ p ^ f) :
    ModelBad PSL(2, GaloisField p f) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  exact modelBad_psl _ (by rw [GaloisField.card p f hf0]; exact hf)

theorem modelBad_of_isTypeL2 {G : Type} [Group G] (h : CFSGOutside.Corpus.Walter.IsTypeL2 G) :
    ModelBad G := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, -, -, h5, -, ⟨e⟩⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (modelBad_psl_galois 2 f (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)).of_mulEquiv e
  · exact (modelBad_psl_galois p f (by omega)).of_mulEquiv e

end PSL

section Ree

open CFSGOutside.Corpus Walter.Ward

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_two_of_even {H : Subgroup G} (h : 2 ∣ Nat.card H) : ∃ t ∈ H, orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, ht⟩, hto⟩ := exists_prime_orderOf_dvd_card' 2 h
  exact ⟨t, ht, by rw [← Subgroup.orderOf_mk t ht]; exact hto⟩

/-- The Sylow `3`-subgroup of a group of Ree type is normalized but not centralized by an involution. -/
theorem bad_three_ree [WardTwoThree] (h : ReeTypeHyp G) (hq : 1 < h.q) (hqe : 2 ∣ h.q - 1) :
    Bad G 3 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 G) := inferInstance
  have key := WardTwoThree.ward_two_three h P
  dsimp only at key
  obtain ⟨-, -, -, hZ, P₁, W, hP₁, -, -, -, hZP₁, -, -, hW, -, hN, ht, -⟩ := key
  obtain ⟨t, htW, ht2⟩ := exists_orderOf_two_of_even (hW ▸ hqe)
  set Z : Subgroup G := (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype
  have hZne : Z ≠ ⊥ := by
    intro h0
    rw [h0, card_bot] at hZ
    omega
  refine ⟨P, fun h0 => hZne (eq_bot_iff.mpr (h0 ▸ (hZP₁.trans hP₁))), P.isPGroup', t, ?_, ?_, 1, ?_⟩
  · rw [hN]; exact mem_sup_right htW
  · intro htc
    obtain ⟨z0, hz0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
    set z : G := (z0 : G)
    have hz : z ∈ Z := z0.2
    have hz1 : z ≠ 1 := fun h' => hz0 (Subtype.ext h')
    have hzP : z ∈ (P : Subgroup G) := hP₁ (hZP₁ hz)
    have : z ∈ (P : Subgroup G) ⊓ centralizer ({t} : Set G) ⊓ Z := by
      refine ⟨⟨hzP, ?_⟩, hz⟩
      show z ∈ centralizer ({t} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp htc) z hzP)
    rw [(ht t htW ht2).2.2.2, mem_bot] at this
    exact hz1 this
  · rw [pow_one, ← ht2, pow_orderOf_eq_one]

/-- A prime dividing the order of one of Ward's Hall subgroups `M±` gives a witness `Bad G p 2`. -/
theorem bad_hall_ree {p : ℕ} [Fact p.Prime] {M W : Subgroup G} (hMc : IsMulCommutative M)
    (hpM : p ∣ Nat.card M) (hW6 : Nat.card W = 6) (hN : normalizer (M : Set G) = M ⊔ W)
    (hfpf : ∀ w ∈ W, w ≠ 1 → M ⊓ centralizer ({w} : Set G) = ⊥) : Bad G p 2 := by
  obtain ⟨w, hwW, hw2⟩ := exists_orderOf_two_of_even (H := W) (by rw [hW6]; norm_num)
  have hwN : w ∈ normalizer (M : Set G) := by rw [hN]; exact mem_sup_right hwW
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw2
  obtain ⟨Q⟩ : Nonempty (Sylow p M) := inferInstance
  have hQn : (Q : Subgroup M).Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hMc.is_comm.comm g n
    rw [this]; exact hn⟩
  have hQc := Sylow.characteristic_of_normal Q hQn
  set H : Subgroup G := (Q : Subgroup M).map M.subtype
  have hHM : H ≤ M := map_subtype_le _
  -- conjugation by an element of `N(M)` maps `H` into `H`
  have hconj : ∀ v ∈ normalizer (M : Set G), ∀ g ∈ H, v * g * v⁻¹ ∈ H := by
    intro v hv g hg
    obtain ⟨m, hm, rfl⟩ := hg
    let φ : MulAut M := M.normalizerMonoidHom ⟨v, hv⟩
    have := (Subgroup.characteristic_iff_map_eq.mp hQc) φ
    have hφm : φ m ∈ (Q : Subgroup M) := by rw [← this]; exact ⟨m, hm, rfl⟩
    exact ⟨φ m, hφm, rfl⟩
  have hwH : w ∈ normalizer (H : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hconj w hwN g, fun hg => ?_⟩
    have := hconj w⁻¹ (inv_mem hwN) _ hg
    rwa [show w⁻¹ * (w * g * w⁻¹) * w⁻¹⁻¹ = g by group] at this
  have hHne : H ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ M.subtype_injective]
    exact Q.ne_bot_of_dvd_card hpM
  refine ⟨H, hHne, Q.isPGroup'.map M.subtype, w, hwH, fun hwc => ?_, 1, ?_⟩
  · obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hHne
    have hzM : (z : G) ∈ M := hHM z.2
    have : (z : G) ∈ M ⊓ centralizer ({w} : Set G) := by
      refine ⟨hzM, ?_⟩
      show (z : G) ∈ centralizer ({w} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hwc) z z.2)
    rw [hfpf w hwW hw1, mem_bot] at this
    exact hz (Subtype.ext this)
  · rw [pow_one, ← hw2, pow_orderOf_eq_one]

/-- A prime `p ≠ 2` of `π` dividing `q² − 1` divides `|PSL(2, q)| = |L|`, `L ≤ C(J)`, so `L` gives a witness. -/
theorem bad_psl_ree {π : Set ℕ} {p : ℕ} [Fact p.Prime] (h : ReeTypeHyp G) (hp2 : p ≠ 2) (hpπ : p ∈ π)
    (h2 : 2 ∉ π) (hq : 4 ≤ h.q) (hqodd : Odd h.q) (hpd : p ∣ (h.q + 1) * (h.q - 1)) :
    ∃ r s : ℕ, r.Prime ∧ r ∈ π ∧ s.Prime ∧ s ∉ π ∧ Bad G r s := by
  have hF : Nat.card (GaloisField h.p h.f) = h.q := GaloisField.card h.p h.f h.f_pos.ne'
  have hcard := card_psl_two_mul_two (GaloisField h.p h.f) (hF ▸ hqodd)
  rw [hF] at hcard
  have hsq : h.q ^ 2 - 1 = (h.q + 1) * (h.q - 1) := by
    have : 1 ≤ h.q := by omega
    have : 1 ≤ h.q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [*]; ring
  have hpL : p ∣ Nat.card PSL(2, GaloisField h.p h.f) := by
    have : p ∣ Nat.card PSL(2, GaloisField h.p h.f) * 2 := by
      rw [hcard, hsq]; exact dvd_mul_of_dvd_right hpd _
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun h' =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')).dvd_of_dvd_mul_right this
  obtain ⟨r, s, hr, hrπ, hs, hsπ, hb⟩ :=
    modelBad_psl (GaloisField h.p h.f) (hF ▸ hq) π h2 p Fact.out hpπ hpL
  exact ⟨r, s, hr, hrπ, hs, hsπ, hb.map (f := h.L.subtype.comp h.iso.symm.toMonoidHom)
    (h.L.subtype_injective.comp h.iso.symm.injective)⟩

/-- A group of Ree type is not π-homogeneous (Arad 1974, p. 7, from Ward 1966). -/
theorem modelBad_ree [WardOrder] [WardTwoThree] [WardFour] (h : ReeTypeHyp G) : ModelBad G := by
  intro π h2 p hp hpπ hpd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨k, hk, hq⟩, hG⟩ := WardOrder.ward_order h
  have hq27 : 27 ≤ h.q := by
    rw [hq]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqodd : Odd h.q := by rw [hq]; exact Odd.pow (by decide)
  have hp2 : p ≠ 2 := fun h' => h2 (h' ▸ hpπ)
  by_cases hp3 : p = 3
  · subst hp3
    refine ⟨3, 2, Nat.prime_three, hpπ, Nat.prime_two, h2, bad_three_ree h (by omega) ?_⟩
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one)
  have hpq : ¬ p ∣ h.q := fun hd =>
    hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow (hq ▸ hd)))
  have h1q : 1 ≤ h.q := by omega
  have hle : h.q ≤ h.q ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1q2 : 1 ≤ h.q ^ 2 := le_trans h1q hle
  have hfac : h.q ^ 3 + 1 = (h.q + 1) * (h.q ^ 2 - h.q + 1) := by
    zify [hle]; ring
  rw [hG] at hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with hpd | hpd
  · rcases (Nat.Prime.dvd_mul hp).mp hpd with hpd | hpd
    · exact absurd (hp.dvd_of_dvd_pow hpd) hpq
    rw [hfac] at hpd
    rcases (Nat.Prime.dvd_mul hp).mp hpd with hpd | hpd
    · -- `p ∣ q + 1`: `p` divides `|L| = |PSL(2, q)|`
      exact bad_psl_ree h hp2 hpπ h2 (by omega) hqodd (dvd_mul_of_dvd_left hpd _)
    · -- `p ∣ q² − q + 1 = |M₊| |M₋|`
      obtain ⟨hfac4, hM⟩ := WardFour.ward_four h hq
      rw [hfac4] at hpd
      rcases (Nat.Prime.dvd_mul hp).mp hpd with hpd | hpd
      · obtain ⟨M, W, hMc, hMcard, -, -, -, -, hW6, -, hN, hfpf⟩ := hM true
        simp only [if_true] at hMcard
        exact ⟨p, 2, hp, hpπ, Nat.prime_two, h2, bad_hall_ree hMc (hMcard ▸ hpd) hW6 hN hfpf⟩
      · obtain ⟨M, W, hMc, hMcard, -, -, -, -, hW6, -, hN, hfpf⟩ := hM false
        simp only [Bool.false_eq_true, if_false] at hMcard
        exact ⟨p, 2, hp, hpπ, Nat.prime_two, h2, bad_hall_ree hMc (hMcard ▸ hpd) hW6 hN hfpf⟩
  · -- `p ∣ q − 1`
    exact bad_psl_ree h hp2 hpπ h2 (by omega) hqodd (dvd_mul_of_dvd_right hpd _)

end Ree

section Simple

open CFSGOutside.Corpus

/-- No nonabelian simple group with dihedral or abelian Sylow `2`-subgroups satisfies `HomP π` with a prime of
`π` dividing its order (Arad 1974, proof of Theorem B(iii)). -/
theorem not_dvd_card_of_isSimpleGroup [WalterStructure] [J2Inverted] [WardOrder] [WardTwoThree]
    [WardFour] [GorensteinWalter] {π : Set ℕ} (h2 : 2 ∉ π) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hS : SylowTwoDihedralOrAbelian G)
    (hH : HomP π G) : ∀ p : ℕ, p.Prime → p ∈ π → ¬ p ∣ Nat.card G := by
  intro p hp hpπ hpd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMB : ModelBad G := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
    rcases hS P with hab | hdih
    · rcases WalterStructure.walter_structure G hnonab P hab with hL2 | hR | e
      · exact modelBad_of_isTypeL2 hL2
      · obtain ⟨hR⟩ := hR; exact modelBad_ree hR
      · obtain ⟨e⟩ := e; exact modelBad_J1.of_mulEquiv e
    · rcases GorensteinWalter.gorenstein_walter G hnonab P hdih with e | ⟨q, k, hq, -, h5, ⟨e⟩⟩
      · obtain ⟨e⟩ := e; exact modelBad_A7.of_mulEquiv e
      · exact (modelBad_psl_galois q k (by omega)).of_mulEquiv e
  obtain ⟨r, s, hr, hrπ, hs, hsπ, hb⟩ := hMB π h2 p hp hpπ hpd
  exact hb.false hH hr hrπ hs hsπ

/-- The abelian case: no nonabelian simple group with abelian Sylow `2`-subgroups satisfies `HomP π` with a
prime of `π` dividing its order. Uses Walter's theorem only (no Gorenstein–Walter). -/
theorem not_dvd_card_of_isSimpleGroup_abelian [WalterStructure] [J2Inverted] [WardOrder]
    [WardTwoThree] [WardFour] {π : Set ℕ} (h2 : 2 ∉ π) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hS : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) (hH : HomP π G) :
    ∀ p : ℕ, p.Prime → p ∈ π → ¬ p ∣ Nat.card G := by
  intro p hp hpπ hpd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMB : ModelBad G := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
    rcases WalterStructure.walter_structure G hnonab P (hS P) with hL2 | hR | e
    · exact modelBad_of_isTypeL2 hL2
    · obtain ⟨hR⟩ := hR; exact modelBad_ree hR
    · obtain ⟨e⟩ := e; exact modelBad_J1.of_mulEquiv e
  obtain ⟨r, s, hr, hrπ, hs, hsπ, hb⟩ := hMB π h2 p hp hpπ hpd
  exact hb.false hH hr hrπ hs hsπ

end Simple

end CFSGOutside.Arad
