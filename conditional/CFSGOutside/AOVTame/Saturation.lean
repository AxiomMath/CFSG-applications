import CFSGOutside.AOVTame.SatGroup
import CFSGOutside.AOVTame.Realize

/-!
# AOV tameness: the fusion system of a finite group is saturated (BLO2, Proposition 1.3)

If `E : S → G` is injective with `E(S) ∈ Syl_p(G)` and realizes `F`, then `F` is saturated.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {S : Type*} [Group S] [Finite S] {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {F : FusionSystem S} {T : Sylow p G} {E : S →* G}

section
variable (hE : Function.Injective E) (hr : E.range = T) (hR : RealizedBy F E)
include hE hr hR

lemma mem_T (x : S) : E x ∈ (T : Subgroup G) := by rw [← hr]; exact ⟨x, rfl⟩

lemma map_le_T (P : Subgroup S) : P.map E ≤ T := by rintro _ ⟨x, -, rfl⟩; exact mem_T hE hr hR x

lemma map_comap_T {R : Subgroup G} (h : R ≤ T) : (R.comap E).map E = R := by
  apply le_antisymm (map_comap_le _ _)
  intro y hy
  have : y ∈ E.range := hr ▸ h hy
  obtain ⟨x, rfl⟩ := this
  exact ⟨x, hy, rfl⟩

lemma conj_iff (P P' : Subgroup S) :
    F.Conj P P' ↔ ∃ g : G, P'.map E = conjSub g (P.map E) := by
  constructor
  · rintro ⟨φ, hφ, ψ, hψ, h1, h2⟩
    obtain ⟨g, hg⟩ := (hR _ _ φ).1 hφ
    refine ⟨g, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (φ (ψ ⟨x, hx⟩) : S) = x := by rw [← MonoidHom.comp_apply, h2]; rfl
      refine ⟨E (ψ ⟨x, hx⟩), ⟨_, (ψ ⟨x, hx⟩).2, rfl⟩, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      rw [← hg, hx']
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨φ ⟨x, hx⟩, (φ ⟨x, hx⟩).2, ?_⟩
      rw [hg]; rfl
  · rintro ⟨g, hg⟩
    obtain ⟨φ, hφ, hφe⟩ := hR.exists_mem hE (P := P) (Q := P') g (fun x => by
      rw [hg]; exact ⟨E x, ⟨x, x.2, rfl⟩, rfl⟩)
    obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem hE (P := P') (Q := P) g⁻¹ (fun x => by
      have : E x ∈ conjSub g (P.map E) := hg ▸ ⟨x, x.2, rfl⟩
      rw [mem_conjSub] at this
      simpa using this)
    refine ⟨φ, hφ, ψ, hψ, ?_, ?_⟩
    · ext x
      apply hE
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [hψe, hφe]; group
    · ext x
      apply hE
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [hφe, hψe]; group

lemma map_normalizer (P : Subgroup S) :
    (normalizer (P : Set S)).map E = normalizer ((P.map E : Subgroup G) : Set G) ⊓ T := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine mem_inf.2 ⟨?_, mem_T hE hr hR s⟩
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s * x * s⁻¹, (mem_normalizer_iff.1 hs x).1 hx, by simp⟩
    · intro hz
      have hzT : z ∈ (T : Subgroup G) := by
        have h1 : E s * z * (E s)⁻¹ ∈ (T : Subgroup G) := map_le_T hE hr hR P hz
        have := mul_mem (mul_mem (inv_mem (mem_T hE hr hR s)) h1) (mem_T hE hr hR s)
        simpa [mul_assoc] using this
      obtain ⟨x, rfl⟩ : z ∈ E.range := hr ▸ hzT
      obtain ⟨x', hx', e⟩ := hz
      have : x' = s * x * s⁻¹ := hE (by rw [e]; simp)
      exact ⟨x, (mem_normalizer_iff.1 hs x).2 (this ▸ hx'), rfl⟩
  · intro hy
    obtain ⟨hyN, hyT⟩ := mem_inf.1 hy
    obtain ⟨s, rfl⟩ : y ∈ E.range := hr ▸ hyT
    refine ⟨s, ?_, rfl⟩
    show s ∈ normalizer (P : Set S)
    rw [mem_normalizer_iff]
    intro x
    have := (mem_normalizer_iff.1 hyN (E x))
    constructor
    · intro hx
      obtain ⟨x', hx', e⟩ := this.1 ⟨x, hx, rfl⟩
      have : x' = s * x * s⁻¹ := hE (by rw [e]; simp)
      exact this ▸ hx'
    · intro hx
      have h2 : E s * E x * (E s)⁻¹ ∈ P.map E := ⟨_, hx, by simp⟩
      obtain ⟨x', hx', e⟩ := this.2 h2
      have : x' = x := hE e
      exact this ▸ hx'

lemma map_centralizer_T (P : Subgroup S) :
    (centralizer (P : Set S)).map E = centralizer ((P.map E : Subgroup G) : Set G) ⊓ T := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine mem_inf.2 ⟨?_, mem_T hE hr hR s⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hs x hx]
  · intro hy
    obtain ⟨hyC, hyT⟩ := mem_inf.1 hy
    obtain ⟨s, rfl⟩ : y ∈ E.range := hr ▸ hyT
    refine ⟨s, ?_, rfl⟩
    show s ∈ centralizer (P : Set S)
    rw [mem_centralizer_iff]
    intro x hx
    have := mem_centralizer_iff.1 hyC (E x) ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact hE this

lemma card_map (P : Subgroup S) : Nat.card (P.map E) = Nat.card P :=
  Nat.card_congr (equivMapOfInjective P E hE).toEquiv.symm

lemma card_normalizer (P : Subgroup S) : Nat.card (normalizer (P : Set S)) =
    Nat.card (normalizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G) : Subgroup G) := by
  rw [← map_normalizer hE hr hR, card_map hE hr hR]

lemma card_centralizer (P : Subgroup S) : Nat.card (centralizer (P : Set S)) =
    Nat.card (centralizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G) : Subgroup G) := by
  rw [← map_centralizer_T hE hr hR, card_map hE hr hR]

lemma fullyNormalized_iff (P : Subgroup S) : F.FullyNormalized P ↔ ∀ g : G,
    conjSub g (P.map E) ≤ T →
      Nat.card (normalizer (conjSub g (P.map E) : Set G) ⊓ (T : Subgroup G) : Subgroup G) ≤
        Nat.card (normalizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G) : Subgroup G) := by
  constructor
  · intro h g hg
    have e := map_comap_T hE hr hR hg
    have hc : F.Conj P ((conjSub g (P.map E)).comap E) := (conj_iff hE hr hR _ _).2 ⟨g, e⟩
    have := h _ hc
    rwa [card_normalizer hE hr hR, card_normalizer hE hr hR, e] at this
  · intro h P' hc
    obtain ⟨g, hg⟩ := (conj_iff hE hr hR _ _).1 hc
    rw [card_normalizer hE hr hR, card_normalizer hE hr hR, hg]
    exact h g (hg ▸ map_le_T hE hr hR P')

lemma fullyCentralized_iff (P : Subgroup S) : F.FullyCentralized P ↔ ∀ g : G,
    conjSub g (P.map E) ≤ T →
      Nat.card (centralizer (conjSub g (P.map E) : Set G) ⊓ (T : Subgroup G) : Subgroup G) ≤
        Nat.card (centralizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G) : Subgroup G) := by
  constructor
  · intro h g hg
    have e := map_comap_T hE hr hR hg
    have hc : F.Conj P ((conjSub g (P.map E)).comap E) := (conj_iff hE hr hR _ _).2 ⟨g, e⟩
    have := h _ hc
    rwa [card_centralizer hE hr hR, card_centralizer hE hr hR, e] at this
  · intro h P' hc
    obtain ⟨g, hg⟩ := (conj_iff hE hr hR _ _).1 hc
    rw [card_centralizer hE hr hR, card_centralizer hE hr hR, hg]
    exact h g (hg ▸ map_le_T hE hr hR P')

omit hr hR in
/-- `N_G(E(P)) → Aut(P)`, `n ↦ E⁻¹ ∘ c_n ∘ E`. -/
noncomputable def rho (P : Subgroup S) :
    normalizer ((P.map E : Subgroup G) : Set G) →* MulAut P where
  toFun n := ((equivMapOfInjective P E hE).trans
    ((Subgroup.normalizerMonoidHom (P.map E)) n)).trans (equivMapOfInjective P E hE).symm
  map_one' := by
    ext x
    simp only [MulEquiv.trans_apply, map_one, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' a b := by
    ext x
    simp only [MulEquiv.trans_apply, map_mul, MulAut.mul_apply, MulEquiv.apply_symm_apply]

omit hr hR in
lemma E_rho (P : Subgroup S) (n : normalizer ((P.map E : Subgroup G) : Set G)) (x : P) :
    E (rho hE P n x) = n * E x * (n : G)⁻¹ := by
  have h1 : (equivMapOfInjective P E hE) (rho hE P n x) =
      (Subgroup.normalizerMonoidHom (P.map E) n) (equivMapOfInjective P E hE x) := by
    simp only [rho, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  have h2 := congrArg Subtype.val h1
  rw [coe_equivMapOfInjective_apply] at h2
  rw [h2]
  change ((n : G) * ((equivMapOfInjective P E hE x : P.map E) : G) * (n : G)⁻¹) = _
  rw [coe_equivMapOfInjective_apply]

lemma rho_range (P : Subgroup S) : (rho hE P).range = F.autF P := by
  ext α
  constructor
  · rintro ⟨n, rfl⟩
    exact (hR P P _).2 ⟨n, fun x => E_rho hE P n x⟩
  · intro hα
    obtain ⟨g, hg⟩ := (hR P P α.toMonoidHom).1 hα
    have hgN : g ∈ normalizer ((P.map E : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨α ⟨x, hx⟩, (α ⟨x, hx⟩).2, hg ⟨x, hx⟩⟩
      · rintro ⟨x', hx', e⟩
        obtain ⟨x, hx⟩ := α.surjective ⟨x', hx'⟩
        have h1 := hg x
        change E (α x) = _ at h1
        rw [hx] at h1
        have : y = E x := by
          have h2 : g * y * g⁻¹ = g * E x * g⁻¹ := by rw [← e, ← h1]
          simpa using h2
        rw [this]; exact ⟨x, x.2, rfl⟩
    refine ⟨⟨g, hgN⟩, ?_⟩
    ext x
    apply hE
    rw [E_rho hE P]
    exact (hg x).symm

lemma autS_eq_map (P : Subgroup S) :
    autS P = ((normalizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G)).subgroupOf
      (normalizer ((P.map E : Subgroup G) : Set G))).map (rho hE P) := by
  ext α
  constructor
  · rintro ⟨s, hs, hα⟩
    have hn : E s ∈ normalizer ((P.map E : Subgroup G) : Set G) ⊓ (T : Subgroup G) := by
      rw [← map_normalizer hE hr hR]; exact ⟨s, hs, rfl⟩
    refine ⟨⟨E s, (mem_inf.1 hn).1⟩, mem_subgroupOf.2 hn, ?_⟩
    ext x
    apply hE
    rw [E_rho hE P, hα x]
    simp
  · rintro ⟨n, hn, rfl⟩
    have hn' := mem_subgroupOf.1 hn
    rw [← map_normalizer hE hr hR] at hn'
    obtain ⟨s, hs, e⟩ := hn'
    refine ⟨s, hs, fun x => ?_⟩
    apply hE
    rw [E_rho hE P, ← e]
    simp

omit hE hr hR in
lemma relIndex_map_range_dvd {A B : Type*} [Group A] [Group B] (f : A →* B) (H : Subgroup A) :
    (H.map f).relIndex f.range ∣ H.index := by
  have : (H.map f).subgroupOf f.range = H.map f.rangeRestrict := by
    ext ⟨y, hy⟩
    simp only [mem_subgroupOf, mem_map, MonoidHom.rangeRestrict]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, e⟩; exact ⟨x, hx, congrArg Subtype.val e⟩
  change ((H.map f).subgroupOf f.range).index ∣ _
  rw [this]
  exact index_map_dvd _ f.rangeRestrict_surjective

lemma map_img {P : Subgroup S} {φ : P →* (⊤ : Subgroup S)} {g : G}
    (hg : ∀ x : P, E (φ x : S) = g * E x * g⁻¹) : (img φ).map E = conjSub g (P.map E) := by
  ext y
  constructor
  · rintro ⟨_, ⟨z, ⟨x, rfl⟩, rfl⟩, rfl⟩
    exact ⟨E x, ⟨x, x.2, rfl⟩, by simp [hg x]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨φ ⟨x, hx⟩, ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩, ?_⟩
    simp [hg ⟨x, hx⟩]

/-- **BLO2, Proposition 1.3.** A fusion system realized by a finite group over a Sylow subgroup
is saturated. -/
theorem saturated : F.Saturated p := by
  refine ⟨fun P hfn => ?_, fun P φ hφ hfc N hN => ?_⟩
  · have hN' := isSylowIn_normalizer T (map_le_T hE hr hR P) ((fullyNormalized_iff hE hr hR P).1 hfn)
    have hC := isSylowIn_centralizer_of_normalizer T hN'
    refine ⟨(fullyCentralized_iff hE hr hR P).2 (fun g _ => card_centralizer_le_of_isSylowIn T hC g),
      ?_, ?_, ?_⟩
    · rw [autS_eq_map hE hr hR, ← rho_range hE hr hR]; exact map_le_range _ _
    · rw [autS_eq_map hE hr hR]
      exact ((T.isPGroup'.to_le inf_le_right).comap_subtype).map _
    · rw [autS_eq_map hE hr hR, ← rho_range hE hr hR]
      exact fun hd => hN'.2.2 (hd.trans (relIndex_map_range_dvd _ _))
  · obtain ⟨g, hg⟩ := (hR P ⊤ φ).1 hφ
    have himg := map_img hE hr hR hg
    have hR'T : conjSub g (P.map E) ≤ T := himg ▸ map_le_T hE hr hR _
    have hC : IsSylowIn p (centralizer (conjSub g (P.map E) : Set G) ⊓ T)
        (centralizer (conjSub g (P.map E) : Set G)) := by
      apply isSylowIn_centralizer T hR'T
      have := (fullyCentralized_iff hE hr hR (img φ)).1 hfc
      rw [himg] at this
      exact this
    have hNmem : ∀ x ∈ N, x ∈ normalizer (P : Set S) ∧ ∃ s ∈ normalizer (img φ : Set S),
        ∀ (r : P) (hr : x * r * x⁻¹ ∈ P), (φ ⟨x * r * x⁻¹, hr⟩ : S) = s * φ r * s⁻¹ := by
      intro x hx
      have : x ∈ (N : Set S) := hx
      rw [hN] at this
      exact this
    have hXN : N.map E ≤ normalizer ((P.map E : Subgroup G) : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      have : E x ∈ (normalizer (P : Set S)).map E := ⟨x, (hNmem x hx).1, rfl⟩
      rw [map_normalizer hE hr hR] at this
      exact (mem_inf.1 this).1
    obtain ⟨c, hc, hcx⟩ := exists_extension T g hC (map_le_T hE hr hR N) hXN (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxN, s, hs, hsφ⟩ := hNmem x hx
      have hy : E s ∈ normalizer (conjSub g (P.map E) : Set G) ⊓ (T : Subgroup G) := by
        rw [← himg, ← map_normalizer hE hr hR]; exact ⟨s, hs, rfl⟩
      refine ⟨E s, hy, ?_⟩
      rintro _ ⟨r, hrP, rfl⟩
      have hr' : x * r * x⁻¹ ∈ P := (mem_normalizer_iff.1 hxN r).1 hrP
      have h1 := hsφ ⟨r, hrP⟩ hr'
      have h2 := hg ⟨x * r * x⁻¹, hr'⟩
      have h3 := hg ⟨r, hrP⟩
      simp only [map_mul, map_inv] at h2
      calc g * (E x * E r * (E x)⁻¹) * g⁻¹ = E (φ ⟨x * r * x⁻¹, hr'⟩ : S) := h2.symm
        _ = E s * E (φ ⟨r, hrP⟩ : S) * (E s)⁻¹ := by rw [h1]; simp
        _ = E s * (g * E r * g⁻¹) * (E s)⁻¹ := by rw [h3])
    obtain ⟨φbar, hφbar, hφbare⟩ := hR.exists_mem hE (P := N) (Q := ⊤) (c * g) (fun x => by
      have := hcx _ ⟨x, x.2, rfl⟩
      rw [← hr] at this
      obtain ⟨y, hy⟩ := this
      exact ⟨y, mem_top _, hy⟩)
    refine ⟨φbar, hφbar, fun x hx => hE ?_⟩
    rw [hφbare ⟨x, hx⟩, hg x]
    have hmem : E (φ x : S) ∈ conjSub g (P.map E) := himg ▸ ⟨φ x, ⟨φ x, ⟨x, rfl⟩, rfl⟩, rfl⟩
    rw [hg x] at hmem
    have hcc := mem_centralizer_iff.1 hc _ hmem
    calc c * g * E x * (c * g)⁻¹ = c * (g * E x * g⁻¹) * c⁻¹ := by group
      _ = (g * E x * g⁻¹) * c * c⁻¹ := by rw [hcc]
      _ = g * E x * g⁻¹ := by group

end

end AndersenOliverVentura.Tame
