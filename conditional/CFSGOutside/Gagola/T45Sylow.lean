import CFSGOutside.Gagola.Lemma44
import CFSGOutside.Gagola.T45Defs

/-!
# Gagola, Theorem 4.5: Sylow subgroups of `H/Z` and the uniqueness of the constituent

* `sylow_comap_data`, `sylow_card_sq`: Sylow subgroups of a group of type f.r. have square order;
* `sylow_card_pow_four`: nonabelian Sylow subgroups under `SylowAb` have order `p⁴`;
* `h16_of_sylowAb`: nonabelian Sylow 2-subgroups have order at most `16`;
* `uniqueness_of_K`: the key descent step, from Corollary 3.6 and Lemma 4.4.
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus

noncomputable section

theorem card_comap_mk {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (S : Subgroup (H ⧸ Z)) :
    Nat.card (S.comap (QuotientGroup.mk' Z)) = Nat.card S * Nat.card Z ∧
      (S.comap (QuotientGroup.mk' Z)).index = S.index := by
  have hidx : (S.comap (QuotientGroup.mk' Z)).index = S.index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)
  refine ⟨?_, hidx⟩
  have h1 := (S.comap (QuotientGroup.mk' Z)).card_mul_index
  have h2 := Z.card_mul_index
  have h3 := S.card_mul_index
  rw [Subgroup.index_eq_card] at h2
  have hSi : 0 < S.index := Nat.pos_of_ne_zero S.index_ne_zero_of_finite
  rw [hidx] at h1
  refine Nat.eq_of_mul_eq_mul_right hSi ?_
  calc Nat.card (S.comap (QuotientGroup.mk' Z)) * S.index = Nat.card H := h1
    _ = Nat.card Z * Nat.card (H ⧸ Z) := h2.symm
    _ = Nat.card Z * (Nat.card S * S.index) := by rw [h3]
    _ = Nat.card S * Nat.card Z * S.index := by ring

theorem sylow_comap_data {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal] {p : ℕ}
    [Fact p.Prime] (P : Sylow p (H ⧸ Z)) :
    Z ≤ (P : Subgroup (H ⧸ Z)).comap (QuotientGroup.mk' Z) ∧
      Nat.card ((P : Subgroup (H ⧸ Z)).comap (QuotientGroup.mk' Z)) = Nat.card P * Nat.card Z ∧
      ((P : Subgroup (H ⧸ Z)).comap (QuotientGroup.mk' Z)).index = (P : Subgroup (H ⧸ Z)).index ∧
      ¬ p ∣ ((P : Subgroup (H ⧸ Z)).comap (QuotientGroup.mk' Z)).index := by
  obtain ⟨h1, h2⟩ := card_comap_mk Z (P : Subgroup (H ⧸ Z))
  refine ⟨?_, h1, h2, ?_⟩
  · intro z hz
    have : QuotientGroup.mk' Z z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    simp [this]
  · rw [h2]; exact P.not_dvd_index

theorem sylow_card_sq {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) {p : ℕ} [hp : Fact p.Prime] (P : Sylow p (H ⧸ Z)) :
    ∃ m, Nat.card P = p ^ (2 * m) := by
  obtain ⟨-, hχ, θ, e, hθ, hres, he⟩ := hfr
  obtain ⟨hZR, hcard, hidx, hnd⟩ := sylow_comap_data Z P
  have hPk := Sylow.card_eq_multiplicity P
  obtain ⟨ζ, -, a, -, ha⟩ := fr_sylow hχ hθ hres he hZR hp.out
    (k := (Nat.card (H ⧸ Z)).factorization p) (by rw [hcard, hPk]) hnd
  rw [hidx] at ha
  have hZi : Z.index = Nat.card P * (P : Subgroup (H ⧸ Z)).index := by
    rw [Subgroup.index_eq_card]; exact ((P : Subgroup (H ⧸ Z)).card_mul_index).symm
  have hPi : 0 < (P : Subgroup (H ⧸ Z)).index := Nat.pos_of_ne_zero P.index_ne_zero_of_finite
  have hae : a ∣ e := by
    have : a ^ 2 ∣ e ^ 2 := ⟨Nat.card P, by rw [he, hZi, ha]; ring⟩
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp this
  obtain ⟨b, rfl⟩ := hae
  have ha0 : 0 < a ^ 2 := by rw [ha]; exact hPi
  have hb : Nat.card P = b ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left ha0 ?_
    calc a ^ 2 * Nat.card P = Nat.card P * (P : Subgroup (H ⧸ Z)).index := by rw [ha]; ring
      _ = (a * b) ^ 2 := by rw [← hZi, he]
      _ = a ^ 2 * b ^ 2 := by ring
  have hbd : b ∣ p ^ ((Nat.card (H ⧸ Z)).factorization p) := by
    rw [← hPk, hb]; exact Dvd.intro_left _ (by ring)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hbd
  exact ⟨j, by rw [hb, hj, ← pow_mul, mul_comm]⟩

theorem isMulCommutative_of_card_lt {G : Type*} [Group G] [Finite G] {p n : ℕ} [hp : Fact p.Prime]
    (hc : Nat.card G = p ^ n) (hn : n ≤ 2) : IsMulCommutative G := by
  interval_cases n
  · have : Nat.card G = 1 := by simpa using hc
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp this).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have hc2 : Nat.card G = p := by simpa using hc
    haveI : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [hc2]; exact hp.out⟩
    haveI : IsCyclic G := isCyclic_of_prime_card (p := Nat.card G) rfl
    letI := IsCyclic.commGroup (α := G)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩
  · haveI : Fintype G := Fintype.ofFinite G
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (by simpa using hc)

theorem sylow_card_pow_four {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal]
    {χ : H → ℂ} (hfr : FullyRamified Z χ) (hS : SylowAb (H ⧸ Z)) {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p (H ⧸ Z)) (hP : ¬ IsMulCommutative (P : Subgroup (H ⧸ Z))) :
    Nat.card P = p ^ 4 := by
  obtain ⟨m, hm⟩ := sylow_card_sq hfr P
  have hm' : Nat.card (P : Subgroup (H ⧸ Z)) = p ^ (2 * m) := hm
  have h1 : 2 < 2 * m := by
    by_contra h
    exact hP (isMulCommutative_of_card_lt (G := (P : Subgroup (H ⧸ Z))) hm' (by omega))
  have h2 : 2 * m < 6 := by
    by_contra h
    refine hP (hS p hp.out ?_ P)
    have h3 : Nat.card (P : Subgroup (H ⧸ Z)) ∣ Nat.card (H ⧸ Z) :=
      Subgroup.card_subgroup_dvd_card (P : Subgroup (H ⧸ Z))
    rw [hm'] at h3
    exact (pow_dvd_pow p (show 6 ≤ 2 * m by omega)).trans h3
  rw [hm]
  congr 1
  omega

theorem h16_of_sylowAb {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (hS : SylowAb (H ⧸ Z)) :
    ∀ P : Sylow 2 (H ⧸ Z), ¬ IsMulCommutative (P : Subgroup (H ⧸ Z)) → Nat.card P ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP
  rw [sylow_card_pow_four hfr hS P hP]
  norm_num

theorem uniqueness_of_K [YoshidaTransfer.{0}] [Order8Nonabelian] [ASevenOrExistsNormalPsl2]
    [CardMulAutPsl2GF] [SL2MinimalFaithfulZsigmondy]
    {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (hS : SylowAb (H ⧸ Z)) {p : ℕ} [hp : Fact p.Prime]
    (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) (hKne : K ≠ ⊤) (hKp : IsPGroup p (H ⧸ K))
    (hno : ∀ (M : Subgroup (K ⧸ Z.subgroupOf K)) [M.Normal],
      IsPGroup p ((K ⧸ Z.subgroupOf K) ⧸ M) → M = ⊤) :
    ∀ τ₁ τ₂ : K → ℂ, τ₁ ∈ Irr K → τ₂ ∈ Irr K → mult (pull K.subtype χ) τ₁ ≠ 0 →
      mult (pull K.subtype χ) τ₂ ≠ 0 → τ₁ = τ₂ := by
  intro τ₁ τ₂ hτ₁ hτ₂ hm₁ hm₂
  have hfr' := hfr
  obtain ⟨-, hχ, θ, e, hθ, hres, he⟩ := hfr'
  obtain ⟨P⟩ : Nonempty (Sylow p (H ⧸ Z)) := inferInstance
  set R : Subgroup H := (P : Subgroup (H ⧸ Z)).comap (QuotientGroup.mk' Z) with hRdef
  obtain ⟨hZR, hcard, hidx, hpR⟩ := sylow_comap_data Z P
  have hRZ : Nat.card R = p ^ (Nat.card (H ⧸ Z)).factorization p * Nat.card Z := by
    rw [hcard, Sylow.card_eq_multiplicity P]
  have hmem : ∀ r : H, r ∈ R ↔ (r : H ⧸ Z) ∈ (P : Subgroup (H ⧸ Z)) := fun r => Iff.rfl
  -- `H = K R`
  have hKR : ∀ h : H, ∃ x ∈ K, ∃ r ∈ R, h = x * r := by
    set g : H ⧸ Z →* H ⧸ K := QuotientGroup.map Z K (MonoidHom.id H) (by simpa using hZK)
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨(h : H ⧸ Z), rfl⟩
    have hdvd := Subgroup.index_map_dvd (f := g) (H := (P : Subgroup (H ⧸ Z))) hg
    obtain ⟨n, hn⟩ := hKp.index ((P : Subgroup (H ⧸ Z)).map g)
    have hn0 : n = 0 := by
      by_contra hn0
      rw [hn] at hdvd
      have : p ∣ (P : Subgroup (H ⧸ Z)).index :=
        (dvd_pow_self p hn0).trans hdvd
      exact P.not_dvd_index this
    have htop : (P : Subgroup (H ⧸ Z)).map g = ⊤ := by
      rw [← Subgroup.index_eq_one, hn, hn0, pow_zero]
    intro h
    have : ((h : H) : H ⧸ K) ∈ (P : Subgroup (H ⧸ Z)).map g := by rw [htop]; trivial
    obtain ⟨y, hy, hgy⟩ := this
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    have hgr : g (r : H ⧸ Z) = (r : H ⧸ K) := rfl
    rw [hgr] at hgy
    have : h * r⁻¹ ∈ K := by
      have := (QuotientGroup.eq_iff_div_mem (N := K)).mp hgy.symm
      simpa [div_eq_mul_inv] using this
    exact ⟨h * r⁻¹, this, r, (hmem r).mpr hy, by group⟩
  by_cases hab : ∀ a ∈ R ⊓ K, ∀ b ∈ R ⊓ K, a * b * a⁻¹ * b⁻¹ ∈ Z
  · exact cor_3_6 hχ hθ hres he hZK hZR hRZ hpR hKR hab hno hτ₁ hτ₂ hm₁ hm₂
  · push Not at hab
    obtain ⟨a, ha, b, hb, hnab⟩ := hab
    have haP : (a : H ⧸ Z) ∈ (P : Subgroup (H ⧸ Z)) := (hmem a).mp ha.1
    have hbP : (b : H ⧸ Z) ∈ (P : Subgroup (H ⧸ Z)) := (hmem b).mp hb.1
    have hncomm : (a : H ⧸ Z) * b ≠ b * a := by
      intro h
      apply hnab
      rw [← QuotientGroup.eq_one_iff]
      have : ((a * b * a⁻¹ * b⁻¹ : H) : H ⧸ Z) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact h
      exact this
    have hPnab : ¬ IsMulCommutative (P : Subgroup (H ⧸ Z)) := by
      rintro ⟨hc⟩
      exact hncomm (congrArg Subtype.val (hc.comm (⟨_, haP⟩ : P) ⟨_, hbP⟩))
    have hP4 := sylow_card_pow_four hfr hS P hPnab
    have hR4 : Nat.card R = p ^ 4 * Nat.card Z := by rw [hcard, hP4]
    set Q : Subgroup (H ⧸ Z) := (R ⊓ K).map (QuotientGroup.mk' Z) with hQdef
    have hQP : Q ≤ (P : Subgroup (H ⧸ Z)) := by
      rw [hQdef, Subgroup.map_le_iff_le_comap]; exact inf_le_left
    have hZRK : Z ≤ R ⊓ K := le_inf hZR hZK
    have hcomapQ : Q.comap (QuotientGroup.mk' Z) = R ⊓ K := by
      rw [hQdef]
      exact Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hZRK)
    have hDQ : Nat.card (R ⊓ K : Subgroup H) = Nat.card Q * Nat.card Z := by
      have := (card_comap_mk Z Q).1
      rwa [hcomapQ] at this
    have hQdvd : Nat.card Q ∣ p ^ 4 := hP4 ▸ Subgroup.card_dvd_of_le hQP
    obtain ⟨j, hj, hQj⟩ := (Nat.dvd_prime_pow hp.out).1 hQdvd
    have haQ : (a : H ⧸ Z) ∈ Q := ⟨a, ha, rfl⟩
    have hbQ : (b : H ⧸ Z) ∈ Q := ⟨b, hb, rfl⟩
    have hQnab : ¬ IsMulCommutative Q := by
      rintro ⟨hc⟩
      exact hncomm (congrArg Subtype.val (hc.comm (⟨_, haQ⟩ : Q) ⟨_, hbQ⟩))
    have hj3 : 3 ≤ j := by
      by_contra h
      exact hQnab (isMulCommutative_of_card_lt hQj (by omega))
    have hj4 : j ≠ 4 := by
      intro hj4
      have hQeq : Q = (P : Subgroup (H ⧸ Z)) :=
        Subgroup.eq_of_le_of_card_ge hQP (by rw [hQj, hP4, hj4])
      apply hKne
      rw [eq_top_iff]
      intro h _
      obtain ⟨x, hx, r, hr, rfl⟩ := hKR h
      have hrQ : (r : H ⧸ Z) ∈ Q := hQeq ▸ (hmem r).mp hr
      obtain ⟨y, hy, hyr⟩ := hrQ
      have hyr' : (y : H ⧸ Z) = r := hyr
      have : y⁻¹ * r ∈ Z := QuotientGroup.eq.mp hyr'
      have hrK : r ∈ K := by
        have := K.mul_mem hy.2 (hZK this)
        simpa using this
      exact K.mul_mem hx hrK
    have hj3' : j = 3 := by omega
    have hD3 : Nat.card (R ⊓ K : Subgroup H) = p ^ 3 * Nat.card Z := by
      rw [hDQ, hQj, hj3']
    exact lemma_4_4 hχ hθ hres he hZK hZR hR4 hpR hKR hD3 ⟨a, ha, b, hb, hnab⟩ hno hτ₁ hτ₂ hm₁ hm₂

end

end CFSGOutside.Gagola
