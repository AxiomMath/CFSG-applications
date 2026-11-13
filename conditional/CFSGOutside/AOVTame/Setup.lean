import CFSGOutside.AOVTame.PhiHom
import CFSGOutside.AOVTame.Induced
import CFSGOutside.AOVTame.FullFusion
import CFSGOutside.AndersenOliverVentura.Factor
import CFSGOutside.AOVTame.Factor2

/-!
# AOV tameness: the groups `G₁ × G₂ → G` and `G₁ → G/G₂`

Setting of the proof of AOV Theorem 3.8: `F = F₁ × F₂` (along `d`) reduced, realized by `G` with
`O(G) = 1`. Goldschmidt's Theorem A gives commuting normal subgroups `G₁, G₂` (the normal closures
of `S₁, S₂`) with `G₁ ∩ G₂ = 1`. Then `μ : G₁ × G₂ → G` and `ν : G₁ → G/G₂` both induce
isomorphisms of centric linking systems (`FusionHom`).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus
open scoped commutatorElement

attribute [local instance] Nat.fact_prime_two

variable {S S₁ S₂ : Type} [Group S] [Group S₁] [Group S₂] [Finite S]
  {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} {d : ProdData S S₁ S₂}
  {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {E : S →* G}

/-- The hypotheses of the "only if" direction of AOV Theorem 3.8, after reducing to `O(G) = 1`. -/
structure Hyp (F : FusionSystem S) (F₁ : FusionSystem S₁) (F₂ : FusionSystem S₂)
    (d : ProdData S S₁ S₂) (T : Sylow 2 G) (E : S →* G) : Prop where
  hS : IsPGroup 2 S
  hprod : IsProdVia F F₁ F₂ d
  hR : RealizedBy F E
  hE : Function.Injective E
  hr : E.range = T
  hodd : goldschmidtOddCore G = ⊥
  /-- `G` has no nontrivial normal 2-subgroup (a consequence of `O₂(F) = 1`, part of
  `F.Reduced 2`). -/
  hO2 : ∀ D : Subgroup G, D.Normal → IsPGroup 2 D → D = ⊥
  /-- Every morphism of `F` is induced by any normal subgroup of odd index containing `T` (a
  consequence of `F.Reduced 2`, `realized_by_normal`). -/
  hnorm : ∀ G₀ : Subgroup G, G₀.Normal → (T : Subgroup G) ≤ G₀ → ¬ 2 ∣ G₀.index →
    ∀ (P Q : Subgroup S) (φ : P →* Q), φ ∈ F.hom P Q → ∃ g ∈ G₀, ∀ x : P, E (φ x) = g * E x * g⁻¹

/-- The normal closure `G₁` of `E(S₁)`. -/
def G₁ (d : ProdData S S₁ S₂) (E : S →* G) : Subgroup G :=
  normalClosure ((E.comp d.ι₁).range : Set G)

/-- The normal closure `G₂` of `E(S₂)`. -/
def G₂ (d : ProdData S S₁ S₂) (E : S →* G) : Subgroup G :=
  normalClosure ((E.comp d.ι₂).range : Set G)

instance : (G₁ d E).Normal := normalClosure_normal
instance : (G₂ d E).Normal := normalClosure_normal

lemma mem_G₁ (a : S₁) : E (d.ι₁ a) ∈ G₁ d E := subset_normalClosure ⟨a, rfl⟩
lemma mem_G₂ (b : S₂) : E (d.ι₂ b) ∈ G₂ d E := subset_normalClosure ⟨b, rfl⟩

/-- `S₁ → G₁`. -/
def e₁ (d : ProdData S S₁ S₂) (E : S →* G) : S₁ →* G₁ d E :=
  (E.comp d.ι₁).codRestrict _ mem_G₁

/-- `S₂ → G₂`. -/
def e₂ (d : ProdData S S₁ S₂) (E : S →* G) : S₂ →* G₂ d E :=
  (E.comp d.ι₂).codRestrict _ mem_G₂

@[simp] lemma coe_e₁ (a : S₁) : (e₁ d E a : G) = E (d.ι₁ a) := rfl
@[simp] lemma coe_e₂ (b : S₂) : (e₂ d E b : G) = E (d.ι₂ b) := rfl

/-- `S → G₁ × G₂`, `x ↦ (x₁, x₂)`. -/
def ε (d : ProdData S S₁ S₂) (E : S →* G) : S →* G₁ d E × G₂ d E :=
  ((e₁ d E).comp d.π₁).prod ((e₂ d E).comp d.π₂)

section
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E)
include h

lemma Hyp.comm : ⁅G₁ d E, G₂ d E⁆ = ⊥ :=
  (normalClosure_inf_eq_bot' h.hS h.hprod h.hR h.hE T h.hr h.hodd h.hO2).1

lemma Hyp.inf : G₁ d E ⊓ G₂ d E = ⊥ :=
  (normalClosure_inf_eq_bot' h.hS h.hprod h.hR h.hE T h.hr h.hodd h.hO2).2

lemma Hyp.commute {a b : G} (ha : a ∈ G₁ d E) (hb : b ∈ G₂ d E) : Commute a b := by
  have h' : (⁅a, b⁆ : G) ∈ ⁅G₁ d E, G₂ d E⁆ := commutator_mem_commutator ha hb
  rw [h.comm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h'
  exact h'

lemma Hyp.eq_one {a : G} (ha₁ : a ∈ G₁ d E) (ha₂ : a ∈ G₂ d E) : a = 1 := by
  have : a ∈ G₁ d E ⊓ G₂ d E := ⟨ha₁, ha₂⟩
  rwa [h.inf, mem_bot] at this

lemma Hyp.mem_T (x : S) : E x ∈ (T : Subgroup G) := by rw [← h.hr]; exact ⟨x, rfl⟩

lemma Hyp.E_decomp (x : S) : E x = E (d.ι₁ (d.π₁ x)) * E (d.ι₂ (d.π₂ x)) := by
  conv_lhs => rw [d.decomp x]
  rw [map_mul]

/-- `T ∩ G₁ = E(S₁)`. -/
lemma Hyp.mem_T_G₁ {t : G} (ht : t ∈ (T : Subgroup G)) (ht₁ : t ∈ G₁ d E) :
    ∃ a, E (d.ι₁ a) = t := by
  rw [← h.hr] at ht
  obtain ⟨x, rfl⟩ := ht
  refine ⟨d.π₁ x, ?_⟩
  have h2 : E (d.ι₂ (d.π₂ x)) = 1 := by
    apply h.eq_one _ (mem_G₂ _)
    have : E (d.ι₂ (d.π₂ x)) = (E (d.ι₁ (d.π₁ x)))⁻¹ * E x := by rw [h.E_decomp x]; group
    rw [this]; exact mul_mem (inv_mem (mem_G₁ _)) ht₁
  rw [h.E_decomp x, h2, mul_one]

/-- `T ∩ G₂ = E(S₂)`. -/
lemma Hyp.mem_T_G₂ {t : G} (ht : t ∈ (T : Subgroup G)) (ht₂ : t ∈ G₂ d E) :
    ∃ b, E (d.ι₂ b) = t := by
  rw [← h.hr] at ht
  obtain ⟨x, rfl⟩ := ht
  refine ⟨d.π₂ x, ?_⟩
  have h2 : E (d.ι₁ (d.π₁ x)) = 1 := by
    apply h.eq_one (mem_G₁ _)
    have : E (d.ι₁ (d.π₁ x)) = E x * (E (d.ι₂ (d.π₂ x)))⁻¹ := by rw [h.E_decomp x]; group
    rw [this]; exact mul_mem ht₂ (inv_mem (mem_G₂ _))
  rw [h.E_decomp x, h2, one_mul]

lemma Hyp.T_le_sup : (T : Subgroup G) ≤ G₁ d E ⊔ G₂ d E := by
  intro t ht
  rw [← h.hr] at ht
  obtain ⟨x, rfl⟩ := ht
  rw [h.E_decomp x]
  exact mul_mem (mem_sup_left (mem_G₁ _)) (mem_sup_right (mem_G₂ _))

/-- Every morphism of `F` is conjugation by an element of `G₁ G₂`. -/
lemma Hyp.realize₀ {P Q : Subgroup S} {ψ : P →* Q} (hψ : ψ ∈ F.hom P Q) :
    ∃ g₁ ∈ G₁ d E, ∃ g₂ ∈ G₂ d E, ∀ x : P, E (ψ x) = (g₁ * g₂) * E x * (g₁ * g₂)⁻¹ := by
  have hidx : ¬ 2 ∣ (G₁ d E ⊔ G₂ d E).index := fun h2 =>
    T.not_dvd_index (h2.trans (index_dvd_of_le h.T_le_sup))
  haveI : (G₁ d E ⊔ G₂ d E).Normal := inferInstance
  obtain ⟨g, hg, hgx⟩ := h.hnorm _ inferInstance h.T_le_sup hidx P Q ψ hψ
  have hg' : g ∈ ((G₁ d E ⊔ G₂ d E : Subgroup G) : Set G) := hg
  rw [mul_normal] at hg'
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hg'
  exact ⟨g₁, hg₁, g₂, hg₂, hgx⟩

/-- Every morphism of `F₁` is conjugation by an element of `G₁`. -/
lemma Hyp.realize₁ {P Q : Subgroup S₁} {φ : P →* Q} (hφ : φ ∈ F₁.hom P Q) :
    ∃ g₁ ∈ G₁ d E, ∀ x : P, E (d.ι₁ (φ x)) = g₁ * E (d.ι₁ x) * g₁⁻¹ := by
  let P' := P.map d.ι₁
  let Q' := Q.map d.ι₁
  have hrP : ∀ x : P', d.π₁ x ∈ P := by
    rintro ⟨_, p, hp, rfl⟩; simp only [d.π₁ι₁]; exact hp
  let r : P' →* P := (d.π₁.comp P'.subtype).codRestrict P hrP
  let ψ : P' →* Q' := (d.ι₁.comp (Q.subtype.comp (φ.comp r))).codRestrict Q'
    (fun x => mem_map_of_mem _ (φ (r x)).2)
  have hle : P'.map d.π₁ ≤ P := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩; rw [d.π₁ι₁]; exact hp
  let φ₁ : P'.map d.π₁ →* Q'.map d.π₁ :=
    (Q.subtype.comp (φ.comp (inclusion hle))).codRestrict (Q'.map d.π₁)
      (fun y => ⟨d.ι₁ (φ (inclusion hle y)), mem_map_of_mem _ (φ _).2, d.π₁ι₁ _⟩)
  have hφ₁ : φ₁ ∈ F₁.hom (P'.map d.π₁) (Q'.map d.π₁) :=
    F₁.mem_of_eq_on hφ hle φ₁ (fun y => rfl)
  have hP₂ : ∀ y : P'.map d.π₂, (y : S₂) = 1 := by
    rintro ⟨_, _, ⟨p, -, rfl⟩, rfl⟩; exact d.π₂ι₁ p
  have hφ₂ : (1 : P'.map d.π₂ →* Q'.map d.π₂) ∈ F₂.hom (P'.map d.π₂) (Q'.map d.π₂) :=
    F₂.conj_mem _ 1 (fun y => by simp [hP₂ y])
  have hψ : ψ ∈ F.hom P' Q' := (h.hprod P' Q' ψ).2 ⟨φ₁, hφ₁, 1, hφ₂, fun x => ⟨by
      show d.π₁ (d.ι₁ (φ (r x) : S₁)) = (φ (inclusion hle _) : S₁)
      rw [d.π₁ι₁]; rfl, by
      show d.π₂ (d.ι₁ (φ (r x) : S₁)) = _
      rw [d.π₂ι₁]; rfl⟩⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := h.realize₀ hψ
  refine ⟨g₁, hg₁, fun x => ?_⟩
  have hx := hg ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩
  have hrx : r ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩ = x := Subtype.ext (d.π₁ι₁ x)
  have : (ψ ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩ : S) = d.ι₁ (φ x) := by
    show d.ι₁ (φ (r _) : S₁) = _; rw [hrx]
  rw [this] at hx
  rw [hx]
  have hc : g₂ * E (d.ι₁ x) * g₂⁻¹ = E (d.ι₁ x) := by
    rw [((h.commute (mem_G₁ (x : S₁)) hg₂).eq).symm]; group
  calc g₁ * g₂ * E (d.ι₁ x) * (g₁ * g₂)⁻¹ = g₁ * (g₂ * E (d.ι₁ x) * g₂⁻¹) * g₁⁻¹ := by group
    _ = _ := by rw [hc]

lemma Hyp.isPGroup₁ : IsPGroup 2 S₁ := h.hS.of_injective d.ι₁ d.ι₁_injective

lemma Hyp.isPGroup₂ : IsPGroup 2 S₂ := h.hS.of_injective d.ι₂ (fun a b e => by
  rw [← d.π₂ι₂ a, e, d.π₂ι₂])

lemma Hyp.range_e₁ : ((e₁ d E).range : Subgroup (G₁ d E)) = (T : Subgroup G).subgroupOf (G₁ d E) := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨a, rfl⟩; exact h.mem_T _
  · intro hx
    obtain ⟨a, ha⟩ := h.mem_T_G₁ hx x.2
    exact ⟨a, Subtype.ext ha⟩

lemma Hyp.range_e₂ : ((e₂ d E).range : Subgroup (G₂ d E)) = (T : Subgroup G).subgroupOf (G₂ d E) := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨a, rfl⟩; exact h.mem_T _
  · intro hx
    obtain ⟨a, ha⟩ := h.mem_T_G₂ hx x.2
    exact ⟨a, Subtype.ext ha⟩

omit h in
lemma not_dvd_relIndex (N : Subgroup G) [N.Normal] : ¬ 2 ∣ (T : Subgroup G).relIndex N := by
  rw [← relIndex_sup_normal]
  exact fun h2 => T.not_dvd_index (h2.trans (relIndex_dvd_index_of_le le_sup_left))

/-- The Sylow subgroup `E(S₁)` of `G₁`. -/
def Hyp.SA : Sylow 2 (G₁ d E) :=
  IsPGroup.toSylow (P := (e₁ d E).range)
    (h.isPGroup₁.of_surjective _ (e₁ d E).rangeRestrict_surjective)
    (by rw [h.range_e₁]; exact not_dvd_relIndex _)

/-- The Sylow subgroup `E(S₂)` of `G₂`. -/
def Hyp.SB : Sylow 2 (G₂ d E) :=
  IsPGroup.toSylow (P := (e₂ d E).range)
    (h.isPGroup₂.of_surjective _ (e₂ d E).rangeRestrict_surjective)
    (by rw [h.range_e₂]; exact not_dvd_relIndex _)

@[simp] lemma Hyp.coe_SA : ((h.SA : Sylow 2 (G₁ d E)) : Subgroup (G₁ d E)) = (e₁ d E).range := rfl
@[simp] lemma Hyp.coe_SB : ((h.SB : Sylow 2 (G₂ d E)) : Subgroup (G₂ d E)) = (e₂ d E).range := rfl

/-- `μ : G₁ × G₂ → G`, `(g₁, g₂) ↦ g₁ g₂`. -/
def Hyp.μ : G₁ d E × G₂ d E →* G :=
  (G₁ d E).subtype.noncommCoprod (G₂ d E).subtype (fun a b => h.commute a.2 b.2)

@[simp] lemma Hyp.μ_apply (x : G₁ d E × G₂ d E) : h.μ x = (x.1 : G) * x.2 := rfl

lemma Hyp.μ_injective : Function.Injective h.μ := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  rw [h.μ_apply] at hab
  have ha : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have ha1 : (a : G) = 1 := h.eq_one a.2 (by rw [ha]; exact inv_mem b.2)
  have hb1 : (b : G) = 1 := by rw [ha1, one_mul] at hab; exact hab
  exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)

lemma Hyp.μ_ε (x : S) : h.μ (ε d E x) = E x := (h.E_decomp x).symm

lemma Hyp.range_ε : (ε d E).range = ((prodSylow h.SA h.SB : Sylow 2 _) : Subgroup _) := by
  ext ⟨a, b⟩
  change _ ↔ a ∈ (e₁ d E).range ∧ b ∈ (e₂ d E).range
  constructor
  · rintro ⟨x, hx⟩
    rw [Prod.ext_iff] at hx
    exact ⟨⟨_, hx.1⟩, ⟨_, hx.2⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    refine ⟨d.ι₁ a * d.ι₂ b, Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      simp [ε, d.π₁ι₁, d.π₁ι₂]
    · apply Subtype.ext
      simp [ε, d.π₂ι₁, d.π₂ι₂]

lemma Hyp.mem_prod_of_μ {y : G₁ d E × G₂ d E} (hy : h.μ y ∈ (T : Subgroup G)) :
    y ∈ ((prodSylow h.SA h.SB : Sylow 2 _) : Subgroup _) := by
  rw [← h.range_ε]
  rw [← h.hr] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, h.μ_injective (by rw [h.μ_ε, hx])⟩

/-- `μ` induces an isomorphism of centric linking systems. -/
lemma Hyp.fusionHom_μ : FusionHom 2 (prodSylow h.SA h.SB) T h.μ where
  map_eq := by
    rw [← h.range_ε, ← MonoidHom.range_comp, ← h.hr]
    congr 1
    ext x; exact h.μ_ε x
  inj x _ y _ e := h.μ_injective e
  fus P hP k hk := by
    let P₀ : Subgroup S := P.comap (ε d E)
    have hP₀ : ∀ x : P₀, k * E x * k⁻¹ ∈ (⊤ : Subgroup S).map E := by
      intro x
      have := hk _ x.2
      rw [h.μ_ε, ← h.hr] at this
      obtain ⟨z, hz⟩ := this
      exact ⟨z, mem_top z, hz⟩
    obtain ⟨ψ, hψ, hψe⟩ := h.hR.exists_mem h.hE k hP₀
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := h.realize₀ hψ
    refine ⟨(⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩), fun x hx => ?_, fun x hx => ?_⟩
    · apply h.mem_prod_of_μ
      have hxr : x ∈ (ε d E).range := h.range_ε ▸ hP hx
      obtain ⟨z, rfl⟩ := hxr
      have := hg ⟨z, hx⟩
      rw [hψe] at this
      rw [map_mul, map_mul, map_inv, h.μ_ε]
      simp only [h.μ_apply]
      rw [← this]
      have := hk _ hx
      rwa [h.μ_ε] at this
    · have hxr : x ∈ (ε d E).range := h.range_ε ▸ hP hx
      obtain ⟨z, rfl⟩ := hxr
      have := hg ⟨z, hx⟩
      rw [hψe] at this
      rw [map_mul, map_mul, map_inv, h.μ_ε]
      simp only [h.μ_apply]
      exact this.symm

end

/-- `G/G₂`. -/
abbrev H (d : ProdData S S₁ S₂) (E : S →* G) := G ⧸ G₂ d E

/-- `ν : G₁ → G/G₂`. -/
def ν (d : ProdData S S₁ S₂) (E : S →* G) : G₁ d E →* H d E :=
  (QuotientGroup.mk' (G₂ d E)).comp (G₁ d E).subtype

/-- The Sylow subgroup `T G₂ / G₂` of `G/G₂`. -/
def Tbar (d : ProdData S S₁ S₂) (E : S →* G) (T : Sylow 2 G) : Sylow 2 (H d E) :=
  T.mapSurjective (QuotientGroup.mk'_surjective (G₂ d E))

/-- `S₁ → G/G₂`. -/
def Ebar (d : ProdData S S₁ S₂) (E : S →* G) : S₁ →* H d E :=
  (QuotientGroup.mk' (G₂ d E)).comp (E.comp d.ι₁)

lemma ν_e₁ (a : S₁) : ν d E (e₁ d E a) = Ebar d E a := rfl

section
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E)
include h

lemma Hyp.quot : Function.Injective (Ebar d E) ∧ (Ebar d E).range = (Tbar d E T : Subgroup (H d E)) ∧
    RealizedBy F₁ (Ebar d E) :=
  realizedBy_fst_quot' h.hS h.hprod h.hR h.hE T h.hr h.hodd h.hO2

/-- `ν` induces an isomorphism of centric linking systems. -/
lemma Hyp.fusionHom_ν : FusionHom 2 h.SA (Tbar d E T) (ν d E) where
  map_eq := by
    rw [h.coe_SA, ← MonoidHom.range_comp]
    exact h.quot.2.1
  inj := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ e
    rw [h.quot.1 e]
  fus P hP k hk := by
    let P₀ : Subgroup S₁ := P.comap (e₁ d E)
    have hP₀ : ∀ x : P₀, k * Ebar d E x * k⁻¹ ∈ (⊤ : Subgroup S₁).map (Ebar d E) := by
      intro x
      have := hk _ x.2
      rw [ν_e₁, ← h.quot.2.1] at this
      obtain ⟨z, hz⟩ := this
      exact ⟨z, mem_top z, hz⟩
    obtain ⟨φ, hφ, hφe⟩ := h.quot.2.2.exists_mem h.quot.1 k hP₀
    obtain ⟨g₁, hg₁, hg⟩ := h.realize₁ hφ
    have key : ∀ x ∈ P, ∃ a : P₀, x = e₁ d E a ∧
        (⟨g₁, hg₁⟩ : G₁ d E) * x * (⟨g₁, hg₁⟩ : G₁ d E)⁻¹ = e₁ d E (φ a) := by
      intro x hx
      obtain ⟨a, rfl⟩ := hP hx
      refine ⟨⟨a, hx⟩, rfl, Subtype.ext ?_⟩
      simp only [coe_mul, coe_inv, coe_e₁]
      exact (hg ⟨a, hx⟩).symm
    refine ⟨⟨g₁, hg₁⟩, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨a, -, e⟩ := key x hx
      rw [e]; exact ⟨_, rfl⟩
    · obtain ⟨a, rfl, e⟩ := key x hx
      rw [e, ν_e₁, ν_e₁, hφe]

end

end AndersenOliverVentura.Tame
