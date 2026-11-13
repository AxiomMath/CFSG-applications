import CFSGOutside.Gagola.Lemma23
import CFSGOutside.Gagola.Cyclic

/-!
# Gagola, Theorem 2.5 (first assertion and (a))

Let `(H, Z, χ)` be a fully ramified triple, `Z ≤ K ⊴ H` and `G = H/K`.

* If a Sylow `p`-subgroup `P` of `G` is cyclic, then `G` has a subgroup of index `|P|` (a `p`-complement).
* (a) If `G` is simple, at most one prime has a nontrivial cyclic Sylow subgroup.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

variable {H : Type*} [Group H] [Fintype H]

/-- `|R| = |R K / K| · |R ∩ K|`. -/
theorem card_eq_card_map_mul (R K : Subgroup H) [K.Normal] :
    Nat.card R = Nat.card (R.map (QuotientGroup.mk' K)) * Nat.card (K.subgroupOf R) := by
  let f : R →* H ⧸ K := (QuotientGroup.mk' K).comp R.subtype
  have hker : f.ker = K.subgroupOf R := by
    ext x
    simp [f, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : f.range = R.map (QuotientGroup.mk' K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← Subgroup.card_ker_mul_card_range f, hker, hrange, mul_comm]

theorem card_subgroupOf_of_le {Z R : Subgroup H} (h : Z ≤ R) : Nat.card (Z.subgroupOf R) = Nat.card Z :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- Dedekind's law for a normal subgroup: `(Q ⊔ Z) ⊓ K = (Q ⊓ K) ⊔ Z` when `Z ≤ K`. -/
theorem sup_inf_of_normal (Q Z K : Subgroup H) [Z.Normal] (hZK : Z ≤ K) :
    (Q ⊔ Z) ⊓ K = (Q ⊓ K) ⊔ Z := by
  apply le_antisymm
  · rintro x ⟨hx, hxK⟩
    have hx' : x ∈ ((Q ⊔ Z : Subgroup H) : Set H) := hx
    rw [Subgroup.mul_normal] at hx'
    obtain ⟨q, hq, z, hz, rfl⟩ := hx'
    have hqK : q ∈ K := by
      have := K.mul_mem hxK (K.inv_mem (hZK hz))
      simpa using this
    exact (Q ⊓ K ⊔ Z).mul_mem (Subgroup.mem_sup_left ⟨hq, hqK⟩) (Subgroup.mem_sup_right hz)
  · exact sup_le (inf_le_inf_right K le_sup_left) (le_inf le_sup_right hZK)

/-- An element normalizing `P` normalizes `P ⊔ Z` for normal `Z`. -/
theorem normalizer_le_normalizer_sup (P Z : Subgroup H) [hZ : Z.Normal] :
    Subgroup.normalizer (P : Set H) ≤ Subgroup.normalizer ((P ⊔ Z : Subgroup H) : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  have key : ∀ g', (∀ h, h ∈ P ↔ g' * h * g'⁻¹ ∈ P) →
      ∀ h ∈ P ⊔ Z, g' * h * g'⁻¹ ∈ P ⊔ Z := by
    intro g' hg' h hh
    have hh' : h ∈ ((P ⊔ Z : Subgroup H) : Set H) := hh
    rw [Subgroup.mul_normal] at hh'
    obtain ⟨a, ha, z, hz, rfl⟩ := hh'
    have : g' * (a * z) * g'⁻¹ = (g' * a * g'⁻¹) * (g' * z * g'⁻¹) := by group
    rw [this]
    exact (P ⊔ Z).mul_mem (Subgroup.mem_sup_left ((hg' a).mp ha))
      (Subgroup.mem_sup_right (hZ.conj_mem z hz g'))
  have hginv : ∀ h, h ∈ P ↔ g⁻¹ * h * g⁻¹⁻¹ ∈ P := by
    intro h
    constructor
    · intro hh
      have := (hg (g⁻¹ * h * g)).mpr (by simpa [mul_assoc] using hh)
      simpa using this
    · intro hh
      have := (hg (g⁻¹ * h * g⁻¹⁻¹)).mp hh
      simpa [mul_assoc] using this
  constructor
  · exact key g hg h
  · intro hh
    have := key g⁻¹ hginv _ hh
    simpa [mul_assoc] using this

section Triple

variable {Z : Subgroup H} {χ : H → ℂ} {θ : Z → ℂ} {e : ℕ}

/-- Lemma 2.3 for `R = Q Z`, `Q` a Sylow `p`-subgroup of `H` containing a Sylow `p`-subgroup `Qk` of
`K`: the hypotheses of `lemma_2_3` hold. -/
theorem lemma_2_3_sylow [hZ : Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (K : Subgroup H) [hK : K.Normal]
    (hZK : Z ≤ K) {p : ℕ} [hp : Fact p.Prime] (Qk : Sylow p K) (Q : Sylow p H)
    (hQk : Qk.map K.subtype ≤ Q) (R : Subgroup H) (hR : R = (Q : Subgroup H) ⊔ Z) :
    ∃ σ ∈ Irr (K.subgroupOf R), ∃ b s : ℕ, 0 < b ∧
      b ^ 2 * s * Nat.card (K.subgroupOf R) = Nat.card R ∧
      (∃ hσ : σ ∈ Irr (K.subgroupOf R), (inertia (N := K.subgroupOf R) σ).index = s ∧
        ∃ φ ∈ Irr (inertia (N := K.subgroupOf R) σ), pull (inclI hσ) φ = (b : ℂ) • σ) ∧
      ∃ T : Subgroup H, K ≤ T ∧ T.index = s := by
  subst hR
  set R : Subgroup H := (Q : Subgroup H) ⊔ Z with hR
  set Qk' : Subgroup H := (Qk : Subgroup K).map K.subtype with hQk'
  -- `Q ∩ K` is the Sylow subgroup `Qk` of `K`
  have hQK : (Q : Subgroup H) ⊓ K = Qk' := by
    have hle : (Qk : Subgroup K) ≤ ((Q : Subgroup H) ⊓ K).subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hQk ⟨x, hx, rfl⟩, x.2⟩
    have hpg : IsPGroup p (((Q : Subgroup H) ⊓ K).subgroupOf K) := by
      have : IsPGroup p ((Q : Subgroup H).subgroupOf K) :=
        Q.isPGroup'.comap_of_injective K.subtype (Subgroup.subtype_injective K)
      refine this.to_le ?_
      intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢; exact hx.1
    have heq := Qk.is_maximal' hpg hle
    rw [hQk', ← heq, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hRK : R ⊓ K = Qk' ⊔ Z := by rw [hR, sup_inf_of_normal _ _ _ hZK, hQK]
  -- the hypotheses of Lemma 2.3
  have hZR : Z ≤ R := le_sup_right
  have hpR : ¬ p ∣ R.index := fun h => Q.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  have hmapZ : R.map (QuotientGroup.mk' Z) = (Q : Subgroup H).map (QuotientGroup.mk' Z) := by
    rw [hR, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  obtain ⟨k, hk⟩ := (Q.isPGroup'.map (QuotientGroup.mk' Z)).exists_card_eq
  have hRZ : Nat.card R = p ^ k * Nat.card Z := by
    rw [card_eq_card_map_mul R Z, hmapZ, hk, card_subgroupOf_of_le hZR]
  have hFrat : NN R K ⊔ K = ⊤ := by
    have h1 := Sylow.normalizer_sup_eq_top Qk
    apply eq_top_iff.mpr
    rw [← h1]
    apply sup_le_sup_right
    show Subgroup.normalizer (Qk' : Set H) ≤ Subgroup.normalizer ((R ⊓ K : Subgroup H) : Set H)
    rw [hRK]
    exact normalizer_le_normalizer_sup Qk' Z
  have hKcop : ¬ p ∣ Nat.card K / Nat.card (R ⊓ K : Subgroup H) := by
    intro hdiv
    apply Qk.not_dvd_index
    have hle : Qk' ≤ R ⊓ K := by rw [hRK]; exact le_sup_left
    have hQkc : Nat.card (Qk : Subgroup K) = Nat.card Qk' :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective K)).symm
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
    obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le (inf_le_right : R ⊓ K ≤ K)
    have hQpos : 0 < Nat.card Qk' := Nat.card_pos
    have hidx : (Qk : Subgroup K).index = n * m := by
      have h1 := (Qk : Subgroup K).card_mul_index
      rw [hQkc, Nat.card_eq_fintype_card (α := K)] at h1
      rw [← Nat.card_eq_fintype_card, hn, hm] at h1
      have : Nat.card Qk' * (Qk : Subgroup K).index = Nat.card Qk' * (n * m) := by
        rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hQpos this
    rw [hn, Nat.mul_div_cancel_left _ (Nat.card_pos)] at hdiv
    rw [hidx]
    exact hdiv.mul_right _
  exact lemma_2_3 hχ hθ hres he K hZK R hZR hp.out hRZ hpR hFrat hKcop

/-- **Gagola, Theorem 2.5, main step**: for a Sylow `p`-subgroup `Q` of `H` whose image in `H/K` is
cyclic, `H` has a subgroup `T ≥ K` whose index is the order of that image. -/
theorem thm_2_5_aux [hZ : Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (K : Subgroup H) [hK : K.Normal]
    (hZK : Z ≤ K) {p : ℕ} [hp : Fact p.Prime] (Qk : Sylow p K) (Q : Sylow p H)
    (hQk : Qk.map K.subtype ≤ Q) (hcyc : IsCyclic (Q.map (QuotientGroup.mk' K))) :
    ∃ T : Subgroup H, K ≤ T ∧ T.index = Nat.card (Q.map (QuotientGroup.mk' K)) := by
  set R : Subgroup H := (Q : Subgroup H) ⊔ Z with hR
  obtain ⟨σ, hσ, b, s, hb, hA, ⟨hσ', hIs, φ, hφ, hφN⟩, T, hKT, hTs⟩ :=
    lemma_2_3_sylow hχ hθ hres he K hZK Qk Q hQk R hR
  -- `b = 1`, by the cyclic-quotient lemma applied in the inertia group
  let f₀ : R →* H ⧸ K := (QuotientGroup.mk' K).comp R.subtype
  have hZbot : Z.map (QuotientGroup.mk' K) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hZK)
  have hrange : f₀.range = (Q : Subgroup H).map (QuotientGroup.mk' K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hR, Subgroup.map_sup, hZbot, sup_bot_eq]
  have hIcyc : IsCyclic ((inertia (N := K.subgroupOf R) σ).map f₀) := by
    have hle : (inertia (N := K.subgroupOf R) σ).map f₀ ≤ (Q : Subgroup H).map (QuotientGroup.mk' K) := by
      rw [← hrange]; exact Subgroup.map_le_range f₀ (inertia (N := K.subgroupOf R) σ)
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨g, hg⟩ := hIcyc.exists_generator
  obtain ⟨a, haI, hag⟩ := (Subgroup.mem_map.mp g.2)
  let a' : inertia (N := K.subgroupOf R) σ := ⟨a, haI⟩
  have hgen : ∀ x : inertia (N := K.subgroupOf R) σ, ∃ (l : K.subgroupOf R) (k : ℕ), x = inclI hσ' l * a' ^ k := by
    intro x
    have hx : (⟨f₀ x, Subgroup.mem_map_of_mem f₀ x.2⟩ : (inertia (N := K.subgroupOf R) σ).map f₀) ∈ Subgroup.zpowers g := hg _
    rw [← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨k, hk⟩ := hx
    have hk' : f₀ (x : R) = f₀ (a' ^ k : inertia (N := K.subgroupOf R) σ) := by
      have := congrArg Subtype.val hk
      simp only [SubmonoidClass.coe_pow] at this
      rw [← this, ← hag]; simp; rfl
    have hmem : ((x : R) * ((a' ^ k : inertia (N := K.subgroupOf R) σ) : R)⁻¹) ∈ K.subgroupOf R := by
      rw [Subgroup.mem_subgroupOf]
      have h0 : f₀ ((x : R) * ((a' ^ k : inertia (N := K.subgroupOf R) σ) : R)⁻¹) = 1 := by
        rw [map_mul, map_inv, hk', mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    refine ⟨⟨_, hmem⟩, k, ?_⟩
    ext
    simp
  -- conjugation by `a` on `L`
  let c : K.subgroupOf R →* K.subgroupOf R := (MulAut.conjNormal ((a' : R)⁻¹)).toMonoidHom
  have hc : ∀ l, inclI hσ' (c l) = a'⁻¹ * inclI hσ' l * a' := by
    intro l
    apply Subtype.ext; apply Subtype.ext
    simp [c, MulAut.conjNormal_apply]
  have hinv : ∀ l, σ (c l) = σ l := by
    intro l
    have h1 : conjN (K.subgroupOf R) (a' : R) σ = σ := haI
    have := congrFun h1 l
    simp only [conjN_apply] at this
    rw [← this]
    congr 1
    apply Subtype.ext
    simp [c, MulAut.conjNormal_apply]
  have hmult : mult (pull (inclI hσ') φ) σ ≠ 0 := by
    rw [hφN, mult_nsmul (irr_isNatComb hσ) b hσ, irr_mult hσ hσ, if_pos rfl, mul_one]
    exact hb.ne'
  have h1 := cyclic_res_eq (inclI hσ') c a' hc hgen hσ hinv hφ hmult
  have h2 : φ 1 = b * σ 1 := by
    have := congrFun hφN 1
    simpa using this
  have hσ1 : σ 1 ≠ 0 := by
    obtain ⟨d, hd, hd'⟩ := irr_one hσ; rw [hd']; exact_mod_cast hd.ne'
  have hb1 : b = 1 := by
    have : ((b : ℂ) - 1) * σ 1 = 0 := by rw [sub_mul, ← h2, h1]; ring
    have := (mul_eq_zero.mp this).resolve_right hσ1
    have : (b : ℂ) = 1 := by linear_combination this
    exact_mod_cast this
  -- conclusion
  refine ⟨T, hKT, ?_⟩
  rw [hTs]
  have hcard := card_eq_card_map_mul R K
  have hmapK : R.map (QuotientGroup.mk' K) = (Q : Subgroup H).map (QuotientGroup.mk' K) := by
    rw [← hrange, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hb1] at hA
  simp only [one_pow, one_mul] at hA
  rw [hmapK] at hcard
  have hLpos : 0 < Nat.card (K.subgroupOf R) := Nat.card_pos
  rw [hcard] at hA
  exact Nat.eq_of_mul_eq_mul_right hLpos hA

/-- **Gagola, Theorem 2.5**: if a Sylow `p`-subgroup `P` of `H/K` is cyclic, then `H/K` has a subgroup of
index `|P|`. -/
theorem thm_2_5 [Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p (H ⧸ K)) (hP : IsCyclic P) :
    ∃ M : Subgroup (H ⧸ K), M.index = Nat.card P := by
  obtain ⟨Qk⟩ := (inferInstance : Nonempty (Sylow p K))
  have hQk : IsPGroup p ((Qk : Subgroup K).map K.subtype) := Qk.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hQk.exists_le_sylow
  set Qb := Q.mapSurjective (QuotientGroup.mk'_surjective K)
  have hQb : (Qb : Subgroup (H ⧸ K)) = (Q : Subgroup H).map (QuotientGroup.mk' K) :=
    Sylow.coe_mapSurjective _ _
  have hcyc : IsCyclic ((Q : Subgroup H).map (QuotientGroup.mk' K)) := by
    rw [← hQb]
    exact isCyclic_of_injective (Sylow.equiv Qb P).toMonoidHom (Sylow.equiv Qb P).injective
  obtain ⟨T, hKT, hT⟩ := thm_2_5_aux hχ hθ hres he K hZK Qk Q hQ hcyc
  refine ⟨T.map (QuotientGroup.mk' K), ?_⟩
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective K) (by rw [QuotientGroup.ker_mk']; exact hKT),
    hT, ← hQb, Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]

/-- **Gagola, Lemma 2.3(a), (c) for a Sylow subgroup of `H/K`**: if `P` is a Sylow `p`-subgroup of `H/K`,
then `|P| = b² s` with `b > 0` and `H/K` has a subgroup of index `s`. -/
theorem thm_2_5_sq [Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p (H ⧸ K)) :
    ∃ b s : ℕ, 0 < b ∧ b ^ 2 * s = Nat.card P ∧ ∃ M : Subgroup (H ⧸ K), M.index = s := by
  obtain ⟨Qk⟩ := (inferInstance : Nonempty (Sylow p K))
  have hQk : IsPGroup p ((Qk : Subgroup K).map K.subtype) := Qk.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hQk.exists_le_sylow
  set R : Subgroup H := (Q : Subgroup H) ⊔ Z with hR
  obtain ⟨σ, hσ, b, s, hb, hA, -, T, hKT, hTs⟩ := lemma_2_3_sylow hχ hθ hres he K hZK Qk Q hQ R hR
  have hZbot : Z.map (QuotientGroup.mk' K) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hZK)
  have hmapK : R.map (QuotientGroup.mk' K) = (Q : Subgroup H).map (QuotientGroup.mk' K) := by
    rw [hR, Subgroup.map_sup, hZbot, sup_bot_eq]
  have hcard := card_eq_card_map_mul R K
  rw [hmapK] at hcard
  set Qb := Q.mapSurjective (QuotientGroup.mk'_surjective K)
  have hQb : (Qb : Subgroup (H ⧸ K)) = (Q : Subgroup H).map (QuotientGroup.mk' K) :=
    Sylow.coe_mapSurjective _ _
  have hPQ : Nat.card P = Nat.card ((Q : Subgroup H).map (QuotientGroup.mk' K)) := by
    rw [← hQb, Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  refine ⟨b, s, hb, ?_, T.map (QuotientGroup.mk' K), ?_⟩
  · rw [hPQ]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card (K.subgroupOf R)) ?_
    rw [hA, hcard]
  · rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective K) (by rw [QuotientGroup.ker_mk']; exact hKT),
      hTs]

/-- A cyclic `q`-subgroup of order `qᵇ` of a simple group with a proper subgroup of index `n` has
`qᵇ ≤ n`. -/
theorem card_le_index_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {M : Subgroup G} (hM : M ≠ ⊤) {Q : Subgroup G} [IsCyclic Q] {q b : ℕ} (hq : q.Prime)
    (hb : 0 < b) (hQ : Nat.card Q = q ^ b) : q ^ b ≤ M.index := by
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := Q)
  have hy' : orderOf y = q ^ b := by rw [orderOf_eq_card_of_forall_mem_zpowers hy, hQ]
  have hyG : orderOf (y : G) = q ^ b := by rw [Subgroup.orderOf_coe, hy']
  -- the action on the cosets of `M` is faithful
  have hcore : M.normalCore = ⊥ := by
    rcases (M.normalCore_normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ M.normalCore_le)) hM
  have hz : (y : G) ^ q ^ (b - 1) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hyG] at this
    have := Nat.le_of_dvd (pow_pos hq.pos _) this
    have := (Nat.pow_le_pow_iff_right hq.one_lt).mp this
    omega
  obtain ⟨c, hc⟩ : ∃ c : G ⧸ M, (y : G) ^ q ^ (b - 1) • c ≠ c := by
    by_contra hcon
    push Not at hcon
    apply hz
    have hker : (y : G) ^ q ^ (b - 1) ∈ (MulAction.toPermHom G (G ⧸ M)).ker := by
      rw [MonoidHom.mem_ker]
      ext x
      exact hcon x
    rw [← Subgroup.normalCore_eq_ker, hcore] at hker
    exact hker
  set d := Function.minimalPeriod (fun x => (y : G) • x) c
  have hd1 : d ∣ q ^ b := by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← hyG, pow_orderOf_eq_one, one_smul]
  have hd2 : ¬ d ∣ q ^ (b - 1) := by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]; exact hc
  obtain ⟨i, hi, hdi⟩ := (Nat.dvd_prime_pow hq).mp hd1
  have hib : i = b := by
    by_contra hne
    apply hd2
    rw [hdi]
    exact Nat.pow_dvd_pow q (by omega)
  letI := Fintype.ofFinite (G ⧸ M)
  have hle : d ≤ Fintype.card (G ⧸ M) := Function.minimalPeriod_le_card
  rw [hdi, hib] at hle
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact hle

/-- **Gagola, Theorem 2.5(a)**: if `H/K` is simple, two distinct primes cannot both have nontrivial
cyclic Sylow subgroups. -/
theorem thm_2_5_a [Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (P : Sylow p (H ⧸ K)) (hP : IsCyclic P) (hP1 : Nat.card P ≠ 1)
    (Q : Sylow q (H ⧸ K)) (hQ : IsCyclic Q) (hQ1 : Nat.card Q ≠ 1) : False := by
  obtain ⟨Mp, hMp⟩ := thm_2_5 hχ hθ hres he K hZK P hP
  obtain ⟨Mq, hMq⟩ := thm_2_5 hχ hθ hres he K hZK Q hQ
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  obtain ⟨b, hb⟩ := Q.isPGroup'.exists_card_eq
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => hP1 (by rw [ha, h, pow_zero]))
  have hb0 : 0 < b := Nat.pos_of_ne_zero (fun h => hQ1 (by rw [hb, h, pow_zero]))
  have hMpne : Mp ≠ ⊤ := by
    intro h; rw [h, Subgroup.index_top] at hMp; exact hP1 hMp.symm
  have hMqne : Mq ≠ ⊤ := by
    intro h; rw [h, Subgroup.index_top] at hMq; exact hQ1 hMq.symm
  have h1 := card_le_index_of_simple hMpne (Q := (Q : Subgroup (H ⧸ K))) hq.out hb0 hb
  have h2 := card_le_index_of_simple hMqne (Q := (P : Subgroup (H ⧸ K))) hp.out ha0 ha
  rw [hMp, ha] at h1
  rw [hMq, hb] at h2
  have heq : p ^ a = q ^ b := le_antisymm h2 h1
  have : p ∣ q ^ b := heq ▸ dvd_pow_self p ha0.ne'
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp (hp.out.dvd_of_dvd_pow this))

end Triple

end

end CFSGOutside.Gagola
