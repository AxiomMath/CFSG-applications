import Mathlib

/-!
# Elementary tools for Craven–Glesser, Lemma 6.11

* `eq_one_of_fix_of_mem`: an automorphism of odd order of a finite 2-group that fixes a subgroup `N`
  pointwise and moves every element only within `N` is trivial.
* `sq_mem_of_isCoatom`, `comm_mem_of_isCoatom`: a maximal subgroup of a finite 2-group is normal of index 2,
  so it contains all squares and commutators.
* `eq_one_of_mem_frattini`: an automorphism of odd order of a finite 2-group acting trivially on
  `P / Φ(P)` is trivial (Burnside).
-/

namespace CFSGOutside.CravenGlesser

open Subgroup

section Coprime

variable {G : Type*} [Group G]

/-- Powers of an automorphism that fixes `x⁻¹ * ψ x`. -/
theorem pow_apply_of_fix (ψ : MulAut G) (x : G) (hfix : ψ (x⁻¹ * ψ x) = x⁻¹ * ψ x) (k : ℕ) :
    (ψ ^ k) x = x * (x⁻¹ * ψ x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, pow_succ', ← mul_assoc,
      mul_inv_cancel_left]

/-- An element of 2-power order whose odd power is trivial is trivial. -/
theorem eq_one_of_pow_odd (hG : IsPGroup 2 G) {n : ℕ} (hn : Odd n) {g : G} (hg : g ^ n = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hG g
  have h1 : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hn)
  have : orderOf g ∣ 1 := by
    rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h2 h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

/-- Coprime action: an automorphism of odd order of a 2-group that fixes `N` pointwise and acts
trivially modulo `N` is trivial. -/
theorem eq_one_of_fix_of_mem (hG : IsPGroup 2 G) (ψ : MulAut G) (hodd : Odd (orderOf ψ))
    (N : Subgroup G) (hfix : ∀ n ∈ N, ψ n = n) (hmov : ∀ x, x⁻¹ * ψ x ∈ N) : ψ = 1 := by
  ext x
  have hpow := pow_apply_of_fix ψ x (hfix _ (hmov x)) (orderOf ψ)
  rw [pow_orderOf_eq_one, MulAut.one_apply] at hpow
  have h1 : (x⁻¹ * ψ x) ^ orderOf ψ = 1 := by
    have := congrArg (x⁻¹ * ·) hpow
    simpa using this.symm
  have := eq_one_of_pow_odd hG hodd h1
  rw [MulAut.one_apply]
  rw [inv_mul_eq_one] at this
  exact this.symm

end Coprime

section Coatom

variable {G : Type*} [Group G] [Finite G]

theorem normal_of_isCoatom (hG : IsPGroup 2 G) {M : Subgroup G} (hM : IsCoatom M) : M.Normal :=
  haveI := hG.isNilpotent
  NormalizerCondition.normal_of_coatom M normalizerCondition_of_isNilpotent hM

/-- The quotient by a maximal subgroup of a finite 2-group has order 2. -/
theorem card_quotient_of_isCoatom (hG : IsPGroup 2 G) {M : Subgroup G} (hM : IsCoatom M) :
    haveI := normal_of_isCoatom hG hM
    Nat.card (G ⧸ M) = 2 := by
  haveI := normal_of_isCoatom hG hM
  have hQ : IsPGroup 2 (G ⧸ M) := hG.to_quotient M
  -- every subgroup of `G ⧸ M` is trivial or everything
  have hsub : ∀ H : Subgroup (G ⧸ M), H = ⊥ ∨ H = ⊤ := by
    intro H
    have hle : M ≤ H.comap (QuotientGroup.mk' M) := by
      intro x hx
      rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact H.one_mem
    rcases eq_or_lt_of_le hle with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
      have : x ∈ H.comap (QuotientGroup.mk' M) := hq
      rw [← h] at this
      simpa [QuotientGroup.eq_one_iff] using this
    · right
      have := hM.2 _ h
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
      have hx : x ∈ H.comap (QuotientGroup.mk' M) := by rw [this]; trivial
      exact hx
  have hnt : Nontrivial (G ⧸ M) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hM.1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact not_subsingleton _ this
  have h2 : 2 ∣ Nat.card (G ⧸ M) := by rw [hn]; exact dvd_pow_self 2 hn0
  haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 (by simpa [Nat.card_eq_fintype_card] using h2)
  rcases hsub (zpowers g) with h | h
  · rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · rw [← hg, ← Nat.card_zpowers, h, Subgroup.card_top]

theorem quotient_sq_eq_one (hG : IsPGroup 2 G) {M : Subgroup G} (hM : IsCoatom M) :
    haveI := normal_of_isCoatom hG hM
    ∀ q : G ⧸ M, q ^ 2 = 1 := by
  haveI := normal_of_isCoatom hG hM
  intro q
  have := pow_card_eq_one' (G := G ⧸ M) (x := q)
  rwa [card_quotient_of_isCoatom hG hM] at this

theorem sq_mem_of_isCoatom (hG : IsPGroup 2 G) {M : Subgroup G} (hM : IsCoatom M) (x : G) :
    x ^ 2 ∈ M := by
  haveI := normal_of_isCoatom hG hM
  have := quotient_sq_eq_one hG hM (x : G ⧸ M)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  exact this

theorem comm_mem_of_isCoatom (hG : IsPGroup 2 G) {M : Subgroup G} (hM : IsCoatom M) (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ M := by
  haveI := normal_of_isCoatom hG hM
  have hsq := quotient_sq_eq_one hG hM
  -- in a group of exponent 2, `a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2`
  have key : ((x * y * x⁻¹ * y⁻¹ : G) : G ⧸ M) = 1 := by
    have hx : ((x : G ⧸ M))⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← sq]; exact hsq _
    have hy : ((y : G ⧸ M))⁻¹ = y := by
      rw [inv_eq_iff_mul_eq_one, ← sq]; exact hsq _
    have hxy := hsq ((x : G ⧸ M) * y)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, hy]
    rw [sq] at hxy
    rw [show (x : G ⧸ M) * y * x * y = (x * y) * (x * y) by group]
    exact hxy
  rwa [QuotientGroup.eq_one_iff] at key

theorem mem_frattini_iff {x : G} : x ∈ frattini G ↔ ∀ M : Subgroup G, IsCoatom M → x ∈ M := by
  simp [frattini, Order.radical, Subgroup.mem_iInf]

theorem sq_mem_frattini (hG : IsPGroup 2 G) (x : G) : x ^ 2 ∈ frattini G :=
  mem_frattini_iff.mpr fun _ hM => sq_mem_of_isCoatom hG hM x

theorem comm_mem_frattini (hG : IsPGroup 2 G) (x y : G) : x * y * x⁻¹ * y⁻¹ ∈ frattini G :=
  mem_frattini_iff.mpr fun _ hM => comm_mem_of_isCoatom hG hM x y

end Coatom

end CFSGOutside.CravenGlesser
