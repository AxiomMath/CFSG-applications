import CFSGOutside.Gagola.Cyclic
import CFSGOutside.Gagola.FullyRamified
import CFSGOutside.Gagola.Clifford

/-!
# A group of type f.r. has no element of order 8 (Gagola 1974, Thm 4.5 ingredient)

Key lemma: if `(H, Z, χ)` is fully ramified, `Z ≤ L ≤ H` and `L/Z` is cyclic of order `d`, then `d ∣ e`.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

theorem exists_constituent' {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsNatComb f)
    (h1 : f 1 ≠ 0) : ∃ ψ ∈ Irr G, mult f ψ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h1
  rw [hf.eq_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun ψ hψ => by rw [hc ψ (mem_irrFinset.mp hψ)]; simp

theorem fr_cyclic_index_dvd {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [hZ : Z.Normal]
    {χ : H → ℂ} (hfr : FullyRamified Z χ) {L : Subgroup H} (hZL : Z ≤ L) (a : L)
    (hgen : ∀ l : L, ∃ (z : Z) (k : ℕ), l = Subgroup.inclusion hZL z * a ^ k)
    {d : ℕ} (hd : Nat.card L = d * Nat.card Z) : ∃ e : ℕ, e ^ 2 = Z.index ∧ d ∣ e := by
  obtain ⟨-, hχ, θ, e, hθ, hres, he⟩ := hfr
  refine ⟨e, he, ?_⟩
  have he0 : (e : ℂ) ≠ 0 := by
    have : e ≠ 0 := by
      rintro rfl
      have := Subgroup.index_ne_zero_of_finite (H := Z)
      simp at he; exact this he.symm
    exact_mod_cast this
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  -- conjugation by a⁻¹ on Z
  let c : Z →* Z :=
    { toFun := fun z => ⟨(a : H)⁻¹ * z * a, by simpa using hZ.conj_mem _ z.2 (a : H)⁻¹⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hc : ∀ z, Subgroup.inclusion hZL (c z) = a⁻¹ * Subgroup.inclusion hZL z * a := by
    intro z; ext; simp [c]
  have hχZ : ∀ w : Z, χ w = e * θ w := fun w => by
    have := congrFun hres w; simpa using this
  have hinv : ∀ z, θ (c z) = θ z := by
    intro z
    have h1 : χ (c z) = χ z := by
      have := (irr_isClassFn hχ).conj_eq (z : H) (a : H)
      simpa [c] using this
    rw [hχZ, hχZ] at h1
    exact mul_left_cancel₀ he0 h1
  -- a constituent of χ_L
  have hχL : IsNatComb (pull L.subtype χ) := (irr_isNatComb hχ).pull _
  obtain ⟨d1, hd1pos, hd1⟩ := irr_one hχ
  obtain ⟨ψ, hψ, hn⟩ := exists_constituent' hχL (by
    simp only [pull_apply, map_one, hd1]; exact_mod_cast hd1pos.ne')
  have hfr1 := fr_ip_mul_card hχ hθ hres he hZL ψ
  rw [← hχL.mult_eq hψ] at hfr1
  set n := mult (pull L.subtype χ) ψ with hn_def
  have hψZ : IsNatComb (pull (Subgroup.inclusion hZL) ψ) := (irr_isNatComb hψ).pull _
  set m := mult (pull (Subgroup.inclusion hZL) ψ) θ with hm_def
  have hmeq : (m : ℂ) = ip (pull (Subgroup.inclusion hZL) ψ) θ := hψZ.mult_eq hθ
  rw [← hmeq] at hfr1
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hfr1
    have hL : (Nat.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have : (n : ℂ) = 0 := by simpa [hL] using hfr1
    exact hn (by exact_mod_cast this)
  -- m ≤ 1
  have hψ1 : ψ 1 = θ 1 := by
    refine cyclic_res_eq (Subgroup.inclusion hZL) c a hc ?_ hθ hinv hψ hm0
    intro x
    obtain ⟨z, k, hk⟩ := hgen x
    exact ⟨z, k, hk⟩
  obtain ⟨d0, hd0pos, hd0⟩ := irr_one hθ
  have hm1 : m ≤ 1 := by
    set g : Z → ℂ := pull (Subgroup.inclusion hZL) ψ - (m : ℂ) • θ with hg
    have hgn : IsNatComb g := by
      refine ⟨isClassFn_sub hψZ.1 (isClassFn_smul _ (irr_isClassFn hθ)), fun ξ hξ => ?_⟩
      rw [hg, ip_sub_left, ip_smul_left, ip_irr hθ hξ, ← hψZ.mult_eq hξ]
      by_cases h : θ = ξ
      · subst h; exact ⟨0, by simp [hm_def]⟩
      · exact ⟨mult (pull (Subgroup.inclusion hZL) ψ) ξ, by simp [h]⟩
    obtain ⟨dg, hdg, -⟩ := hgn.one_eq
    have h1 : g 1 = (d0 : ℂ) * (1 - m) := by
      simp only [hg, Pi.sub_apply, Pi.smul_apply, pull_apply, map_one, hψ1, hd0, smul_eq_mul]
      ring
    rw [h1] at hdg
    have : (d0 : ℤ) * (1 - m) = dg := by exact_mod_cast hdg
    nlinarith
  have hm : m = 1 := by omega
  rw [hm, hd] at hfr1
  have : (n : ℂ) * (d * Nat.card Z) = e * Nat.card Z * 1 := by
    rw [← Nat.cast_mul, hfr1]; push_cast; ring
  have h2 : n * d * Nat.card Z = e * Nat.card Z := by
    have : ((n * d * Nat.card Z : ℕ) : ℂ) = ((e * Nat.card Z : ℕ) : ℂ) := by
      push_cast; linear_combination this
    exact_mod_cast this
  have h3 : n * d = e := Nat.eq_of_mul_eq_mul_right hZpos h2
  exact ⟨n, by rw [← h3]; ring⟩

theorem fr_no_order_eight {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (P : Sylow 2 (H ⧸ Z)) (hP : Nat.card P = 16)
    (x : H ⧸ Z) (hx : x ∈ (P : Subgroup (H ⧸ Z))) : orderOf x ≠ 8 := by
  intro h8
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set L : Subgroup H := (Subgroup.zpowers (g : H ⧸ Z)).comap (QuotientGroup.mk' Z) with hL
  have hZL : Z ≤ L := fun z hz => by
    simp [hL, (QuotientGroup.eq_one_iff z).mpr hz, Subgroup.one_mem]
  have hLmem : ∀ l : H, l ∈ L ↔ (l : H ⧸ Z) ∈ Subgroup.zpowers (g : H ⧸ Z) := fun l => Iff.rfl
  have hgL : g ∈ L := (hLmem g).mpr (Subgroup.mem_zpowers _)
  set y : H ⧸ Z := (g : H ⧸ Z) with hy
  have hcard : Nat.card L = 8 * Nat.card Z := by
    have h1 := L.card_mul_index
    have hidx : L.index = (Subgroup.zpowers y).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)
    have h2 := (Subgroup.zpowers y).card_mul_index
    have h3 := Z.card_mul_index
    have h4 : Nat.card (Subgroup.zpowers y) = 8 := by rw [Nat.card_zpowers, h8]
    have h5 : Z.index = Nat.card (H ⧸ Z) := rfl
    have hpos : 0 < (Subgroup.zpowers y).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    rw [h4] at h2
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← h3, h5, ← h2]; ring
  obtain ⟨e, he, hde⟩ := fr_cyclic_index_dvd hfr hZL ⟨g, hgL⟩ (by
    intro l
    have hl : (l : H ⧸ Z) ∈ Subgroup.zpowers y := l.2
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hl
    obtain ⟨k, hk⟩ := hl
    have hz : (l : H) * ((g : H) ^ k)⁻¹ ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      simp [hy] at hk ⊢
      rw [hk]; simp
    refine ⟨⟨_, hz⟩, k, ?_⟩
    ext; simp) hcard
  have hN0 : Nat.card (H ⧸ Z) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (H ⧸ Z)).factorization 2 = 4 := by
    have h := P.card_eq_multiplicity
    rw [hP] at h
    have h' : 2 ^ 4 = 2 ^ (Nat.card (H ⧸ Z)).factorization 2 := by simpa using h
    exact (Nat.pow_right_injective (le_refl 2) h').symm
  obtain ⟨c, rfl⟩ := hde
  have hdvd : 2 ^ 6 ∣ Nat.card (H ⧸ Z) := ⟨c ^ 2, by
    have : Z.index = Nat.card (H ⧸ Z) := rfl
    rw [← this, ← he]; ring⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).mp hdvd
  omega

end

end CFSGOutside.Gagola
