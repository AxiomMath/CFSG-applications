import CFSGOutside.AndersenOliverVentura.OddCore
import CFSGOutside.Corpus.GoldschmidtTheoremA

/-!
# Andersen–Oliver–Ventura: a factor of a realizable product is realizable

The "only if" half of the realizability clause of AOV Theorem 3.8. Suppose `F = F₁ × F₂` is
realized by a finite group `G` with `O(G) = 1`, and `F` has no nontrivial normal subgroup. The
images `A₁, A₂` of `S₁, S₂` are strongly closed, commute and meet trivially, so by Goldschmidt's
Theorem A their normal closures `G₁, G₂` commute. Then `G₁ ∩ G₂` is an abelian normal subgroup;
its odd part lies in `O(G) = 1`, so it is a normal 2-subgroup of `G` and hence normal in `F`; so
`G₁ ∩ G₂ = 1`. Finally `G/G₂` realizes `F₁`.

The decomposition `S = S₁ × S₂` is recorded abstractly by `ProdData`, so that the second factor is
handled by `ProdData.swap`.
-/

namespace AndersenOliverVentura

open Subgroup CFSGOutside.Corpus
open scoped commutatorElement

universe u v w

/-- Projections and injections exhibiting `S` as a direct product `S₁ × S₂`. -/
structure ProdData (S : Type u) (S₁ : Type v) (S₂ : Type w) [Group S] [Group S₁] [Group S₂] where
  π₁ : S →* S₁
  π₂ : S →* S₂
  ι₁ : S₁ →* S
  ι₂ : S₂ →* S
  π₁ι₁ : ∀ a, π₁ (ι₁ a) = a
  π₂ι₁ : ∀ a, π₂ (ι₁ a) = 1
  π₁ι₂ : ∀ b, π₁ (ι₂ b) = 1
  π₂ι₂ : ∀ b, π₂ (ι₂ b) = b
  decomp : ∀ x, x = ι₁ (π₁ x) * ι₂ (π₂ x)

namespace ProdData

variable {S : Type u} {S₁ : Type v} {S₂ : Type w} [Group S] [Group S₁] [Group S₂]
  (d : ProdData S S₁ S₂)

lemma comm (a : S₁) (b : S₂) : d.ι₂ b * d.ι₁ a = d.ι₁ a * d.ι₂ b := by
  rw [d.decomp (d.ι₂ b * d.ι₁ a)]
  simp [d.π₁ι₁, d.π₂ι₁, d.π₁ι₂, d.π₂ι₂]

lemma ι₁_injective : Function.Injective d.ι₁ := fun a b h => by
  rw [← d.π₁ι₁ a, h, d.π₁ι₁]

lemma range_ι₂_normal : d.ι₂.range.Normal := ⟨by
  rintro _ ⟨b, rfl⟩ s
  refine ⟨d.π₂ s * b * (d.π₂ s)⁻¹, ?_⟩
  set a := d.π₁ s
  set c := d.π₂ s
  have hc := d.comm a (c * b * c⁻¹)
  rw [d.decomp s]
  simp only [map_mul, map_inv] at hc ⊢
  calc d.ι₂ c * d.ι₂ b * (d.ι₂ c)⁻¹
      = (d.ι₂ c * d.ι₂ b * (d.ι₂ c)⁻¹ * d.ι₁ a) * (d.ι₁ a)⁻¹ := by group
    _ = d.ι₁ a * d.ι₂ c * d.ι₂ b * (d.ι₁ a * d.ι₂ c)⁻¹ := by rw [hc]; group⟩

/-- The same decomposition with the factors exchanged. -/
def swap : ProdData S S₂ S₁ where
  π₁ := d.π₂
  π₂ := d.π₁
  ι₁ := d.ι₂
  ι₂ := d.ι₁
  π₁ι₁ := d.π₂ι₂
  π₂ι₁ := d.π₁ι₂
  π₁ι₂ := d.π₂ι₁
  π₂ι₂ := d.π₁ι₁
  decomp x := by rw [d.comm]; exact d.decomp x

/-- The decomposition `S₁ × S₂`. -/
def prod (S₁ : Type v) (S₂ : Type w) [Group S₁] [Group S₂] : ProdData (S₁ × S₂) S₁ S₂ where
  π₁ := MonoidHom.fst S₁ S₂
  π₂ := MonoidHom.snd S₁ S₂
  ι₁ := MonoidHom.inl S₁ S₂
  ι₂ := MonoidHom.inr S₁ S₂
  π₁ι₁ _ := rfl
  π₂ι₁ _ := rfl
  π₁ι₂ _ := rfl
  π₂ι₂ _ := rfl
  decomp x := by ext <;> simp

end ProdData

variable {S : Type u} {S₁ : Type v} {S₂ : Type w} [Group S] [Group S₁] [Group S₂]

/-- `F = F₁ × F₂` along the decomposition `d`. -/
def IsProdVia (F : FusionSystem S) (F₁ : FusionSystem S₁) (F₂ : FusionSystem S₂)
    (d : ProdData S S₁ S₂) : Prop :=
  ∀ (P Q : Subgroup S) (ψ : P →* Q), ψ ∈ F.hom P Q ↔
    ∃ φ₁ ∈ F₁.hom (P.map d.π₁) (Q.map d.π₁), ∃ φ₂ ∈ F₂.hom (P.map d.π₂) (Q.map d.π₂),
      ∀ x : P, d.π₁ (ψ x) = φ₁ ⟨d.π₁ x, mem_map_of_mem _ x.2⟩ ∧
        d.π₂ (ψ x) = φ₂ ⟨d.π₂ x, mem_map_of_mem _ x.2⟩

lemma IsProdVia.swap {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}
    {d : ProdData S S₁ S₂} (h : IsProdVia F F₁ F₂ d) : IsProdVia F F₂ F₁ d.swap := by
  intro P Q ψ
  rw [h P Q ψ]
  constructor
  · rintro ⟨φ₁, h₁, φ₂, h₂, hx⟩
    exact ⟨φ₂, h₂, φ₁, h₁, fun x => (hx x).symm⟩
  · rintro ⟨φ₂, h₂, φ₁, h₁, hx⟩
    exact ⟨φ₁, h₁, φ₂, h₂, fun x => (hx x).symm⟩

lemma IsProduct.isProdVia {F : FusionSystem (S₁ × S₂)} {F₁ : FusionSystem S₁}
    {F₂ : FusionSystem S₂} (h : IsProduct F F₁ F₂) : IsProdVia F F₁ F₂ (ProdData.prod S₁ S₂) := by
  intro P Q ψ
  rw [h P Q ψ]
  simp only [Prod.ext_iff]
  rfl

section Core

variable {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}
  {d : ProdData S S₁ S₂} {G : Type} [Group G] {E : S →* G}

/-- The image of `S₁` is strongly closed in `E(S)` with respect to `G`. -/
lemma stronglyClosed_image (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E)
    (hE : Function.Injective E) {T : Subgroup G} (hrange : E.range = T) :
    fusionStronglyClosed ((E.comp d.ι₁).range : Set G) T := by
  rintro _ ⟨s, rfl⟩ g hg
  set x := d.ι₁ s
  have hgx : g⁻¹ * E x * g ∈ T := hg
  obtain ⟨φ, hφ, hφe⟩ := hR.exists_mem (P := zpowers x) (Q := ⊤) hE g⁻¹ (by
    rintro ⟨_, k, rfl⟩
    have : g⁻¹ * E (x ^ k) * g⁻¹⁻¹ = (g⁻¹ * E x * g) ^ k := by
      have h := map_zpow (MulAut.conj g⁻¹) (E x) k
      simp only [MulAut.conj_apply, inv_inv] at h
      rw [inv_inv, map_zpow]; exact h
    simp only
    rw [this]
    have hk : (g⁻¹ * E x * g) ^ k ∈ T := zpow_mem hgx k
    rw [← hrange] at hk
    obtain ⟨y, hy⟩ := hk
    exact ⟨y, mem_top _, hy⟩)
  obtain ⟨φ₁, -, φ₂, -, hx⟩ := (hprod _ _ φ).1 hφ
  have hxP : x ∈ zpowers x := mem_zpowers x
  have h2 := (hx ⟨x, hxP⟩).2
  have h1 : (⟨d.π₂ x, mem_map_of_mem _ hxP⟩ : (zpowers x).map d.π₂) = 1 :=
    Subtype.ext (d.π₂ι₁ s)
  rw [h1, map_one] at h2
  have hdec := d.decomp (φ ⟨x, hxP⟩ : S)
  rw [show d.π₂ (φ ⟨x, hxP⟩ : S) = 1 from h2, map_one, mul_one] at hdec
  have he := hφe ⟨x, hxP⟩
  rw [inv_inv] at he
  show g⁻¹ * E x * g ∈ (E.comp d.ι₁).range
  rw [← he, hdec]
  exact ⟨_, rfl⟩

omit [Group S₁] [Group S₂] in
/-- A normal subgroup of `G` inside `E(S)` is (the image of) a normal subgroup of `F`. -/
lemma isNormalSubgroup_comap (hR : RealizedBy F E) (hE : Function.Injective E) {T : Subgroup G}
    (hrange : E.range = T) {D : Subgroup G} [hD : D.Normal] (hDT : D ≤ T) :
    F.IsNormalSubgroup (D.comap E) := by
  have hDT' : ∀ y ∈ D, ∃ z ∈ D.comap E, E z = y := by
    intro y hy
    have : y ∈ E.range := by rw [hrange]; exact hDT hy
    obtain ⟨z, rfl⟩ := this
    exact ⟨z, hy, rfl⟩
  haveI hD' : (D.comap E).Normal := hD.comap E
  refine ⟨hD', fun Q R φ hφ => ?_⟩
  obtain ⟨g, hg⟩ := (hR Q R φ).1 hφ
  obtain ⟨φbar, hφbar, hφbare⟩ := hR.exists_mem hE (P := D.comap E ⊔ Q) (Q := D.comap E ⊔ R) g (by
    rintro ⟨z, hz⟩
    have hz' : z ∈ ((Q ⊔ D.comap E : Subgroup S) : Set S) := by rw [sup_comm]; exact hz
    rw [mul_normal] at hz'
    obtain ⟨q, hq, e, he, rfl⟩ := hz'
    obtain ⟨e₂, he₂, he₂e⟩ := hDT' (g * E e * g⁻¹) (hD.conj_mem _ he g)
    refine ⟨φ ⟨q, hq⟩ * e₂, mul_mem (mem_sup_right (φ ⟨q, hq⟩).2) (mem_sup_left he₂), ?_⟩
    simp only [map_mul, he₂e]
    rw [show E (φ ⟨q, hq⟩) = g * E q * g⁻¹ from hg ⟨q, hq⟩]
    group)
  refine ⟨φbar, hφbar, fun x => hE ?_, ?_⟩
  · rw [hφbare, hg x]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show E (φbar z : S) ∈ D
      rw [hφbare]; exact hD.conj_mem _ hz g
    · intro hy
      obtain ⟨z, hz, hze⟩ := hDT' (g⁻¹ * E y * g) (by
        have := hD.conj_mem _ hy g⁻¹; rwa [inv_inv] at this)
      refine ⟨⟨z, mem_sup_left hz⟩, hz, hE ?_⟩
      rw [hφbare]; simp only; rw [hze]; group

/-- The normal closures of the images of `S₁` and `S₂` commute and meet trivially. -/
lemma normalClosure_inf_eq_bot [GoldschmidtTheoremA] [Finite G] (hS : IsPGroup 2 S)
    (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E) (hE : Function.Injective E)
    (T : Sylow 2 G) (hrange : E.range = T) (hodd : goldschmidtOddCore G = ⊥)
    (hO : ∀ D : Subgroup S, F.IsNormalSubgroup D → D = ⊥) :
    ⁅normalClosure ((E.comp d.ι₁).range : Set G), normalClosure ((E.comp d.ι₂).range : Set G)⁆ = ⊥ ∧
    normalClosure ((E.comp d.ι₁).range : Set G) ⊓ normalClosure ((E.comp d.ι₂).range : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A₁ := (E.comp d.ι₁).range
  set A₂ := (E.comp d.ι₂).range
  have hAT₁ : A₁ ≤ T := by rintro _ ⟨a, rfl⟩; rw [← hrange]; exact ⟨_, rfl⟩
  have hAT₂ : A₂ ≤ T := by rintro _ ⟨a, rfl⟩; rw [← hrange]; exact ⟨_, rfl⟩
  have hsc₁ := stronglyClosed_image hprod hR hE hrange
  have hsc₂ := stronglyClosed_image hprod.swap hR hE hrange
  have hcomm : ⁅A₁, A₂⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply, ← map_mul, d.comm]
  have hdisj : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h1 : d.ι₂ b = d.ι₁ a := hE hb
    have h2 := congrArg d.π₁ h1
    rw [d.π₁ι₂, d.π₁ι₁] at h2
    rw [mem_bot, MonoidHom.comp_apply, ← h2, map_one, map_one]
  have hG := GoldschmidtTheoremA.theoremA T T hAT₁ hAT₂ hsc₁ hsc₂ hcomm hdisj
  rw [hodd, le_bot_iff] at hG
  refine ⟨hG, ?_⟩
  set G₁ := normalClosure (A₁ : Set G)
  set G₂ := normalClosure (A₂ : Set G)
  set D := G₁ ⊓ G₂
  have hcD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    have : (⁅x, y⁆ : G) ∈ ⁅G₁, G₂⁆ := commutator_mem_commutator hx.1 hy.2
    rw [hG, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hn : Nat.card D ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  let Dm : Subgroup G :=
    { carrier := {x | x ∈ D ∧ x ^ m = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := by
        rintro x y ⟨hx, hxm⟩ ⟨hy, hym⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [(Commute.mul_pow (hcD x hx y hy) m), hxm, hym, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxm⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxm, inv_one]⟩ }
  have hDmn : Dm.Normal := ⟨fun x ⟨hx, hxm⟩ g =>
    ⟨(inferInstance : D.Normal).conj_mem x hx g, by rw [conj_pow, hxm]; group⟩⟩
  have hDmo : Odd (Nat.card Dm) := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hev
    have hzm : z ^ m = 1 := Subtype.ext z.2.2
    have := orderOf_dvd_of_pow_eq_one hzm
    rw [hz] at this
    exact hm.not_two_dvd_nat this
  have hDm : Dm ≤ ⊥ := hodd ▸ le_sSup ⟨hDmn, hDmo⟩
  have hDp : IsPGroup 2 D := by
    intro x
    refine ⟨k, Subtype.ext ?_⟩
    have hx1 : (x : G) ^ (2 ^ k * m) = 1 := by
      rw [← hkm]
      have := pow_card_eq_one' (G := D) (x := x)
      exact congrArg Subtype.val this
    have : (x : G) ^ 2 ^ k ∈ Dm := ⟨pow_mem x.2 _, by rw [← pow_mul, hx1]⟩
    simpa using hDm this
  have hDT : D ≤ T := hDp.le_sylow_of_normal T
  have hDc := hO _ (isNormalSubgroup_comap hR hE hrange hDT)
  rw [eq_bot_iff]
  intro y hy
  have : y ∈ E.range := by rw [hrange]; exact hDT hy
  obtain ⟨z, rfl⟩ := this
  have hz : z ∈ D.comap E := hy
  rw [hDc, mem_bot] at hz
  rw [hz, map_one]; exact one_mem _

/-- **Factor lemma.** If `F = F₁ × F₂` has no nontrivial normal subgroup and is realized by `G` with
`O(G) = 1`, then `G / G₂` realizes `F₁`, where `G₂` is the normal closure of the image of `S₂`. -/
lemma realizedBy_fst_quot [GoldschmidtTheoremA] [Finite G] (hS : IsPGroup 2 S)
    (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E) (hE : Function.Injective E)
    (T : Sylow 2 G) (hrange : E.range = T) (hodd : goldschmidtOddCore G = ⊥)
    (hO : ∀ D : Subgroup S, F.IsNormalSubgroup D → D = ⊥) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    Function.Injective ((QuotientGroup.mk' (normalClosure ((E.comp d.ι₂).range : Set G))).comp
      (E.comp d.ι₁)) ∧
    ((QuotientGroup.mk' (normalClosure ((E.comp d.ι₂).range : Set G))).comp (E.comp d.ι₁)).range =
      ((T.mapSurjective (QuotientGroup.mk'_surjective (normalClosure ((E.comp d.ι₂).range : Set G))) :
        Sylow 2 (G ⧸ normalClosure ((E.comp d.ι₂).range : Set G))) :
          Subgroup (G ⧸ normalClosure ((E.comp d.ι₂).range : Set G))) ∧
    RealizedBy F₁ ((QuotientGroup.mk' (normalClosure ((E.comp d.ι₂).range : Set G))).comp
      (E.comp d.ι₁)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hdisj⟩ := normalClosure_inf_eq_bot hS hprod hR hE T hrange hodd hO
  set G₁ := normalClosure ((E.comp d.ι₁).range : Set G)
  set G₂ := normalClosure ((E.comp d.ι₂).range : Set G)
  let π := QuotientGroup.mk' G₂
  have hA₁ : ∀ a, E (d.ι₁ a) ∈ G₁ := fun a => subset_normalClosure ⟨a, rfl⟩
  have hA₂ : ∀ b, E (d.ι₂ b) ∈ G₂ := fun b => subset_normalClosure ⟨b, rfl⟩
  have hπ₂ : ∀ b, π (E (d.ι₂ b)) = 1 := fun b => (QuotientGroup.eq_one_iff _).2 (hA₂ b)
  have hπE : ∀ x, π (E x) = π (E (d.ι₁ (d.π₁ x))) := fun x => by
    conv_lhs => rw [d.decomp x]
    rw [map_mul, map_mul, hπ₂, mul_one]
  have hET : ∀ x, E x ∈ (T : Subgroup G) := fun x => by rw [← hrange]; exact ⟨x, rfl⟩
  let E₁ : S₁ →* G ⧸ G₂ := π.comp (E.comp d.ι₁)
  have hinj : Function.Injective E₁ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h2 : E (d.ι₁ a) ∈ G₂ := (QuotientGroup.eq_one_iff _).1 ha
    have : E (d.ι₁ a) ∈ G₁ ⊓ G₂ := ⟨hA₁ a, h2⟩
    rw [hdisj, mem_bot] at this
    have h3 : d.ι₁ a = 1 := (injective_iff_map_eq_one E).1 hE _ this
    rw [← d.π₁ι₁ a, h3, map_one]
  let T₁ : Sylow 2 (G ⧸ G₂) := T.mapSurjective (QuotientGroup.mk'_surjective G₂)
  have hrange₁ : E₁.range = T₁ := by
    rw [Sylow.coe_mapSurjective]
    ext y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨_, hET _, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      rw [← hrange] at ht
      obtain ⟨x, rfl⟩ := ht
      exact ⟨d.π₁ x, (hπE x).symm⟩
  -- `T ∩ G₂` lies in the image of `S₂`.
  have hTG₂ : ∀ x, E x ∈ G₂ → x = d.ι₂ (d.π₂ x) := by
    intro x hx
    have h1 : E (d.ι₁ (d.π₁ x)) = E x * (E (d.ι₂ (d.π₂ x)))⁻¹ := by
      have hd := congrArg E (d.decomp x)
      rw [map_mul] at hd
      rw [hd]; group
    have h2 : E (d.ι₁ (d.π₁ x)) ∈ G₁ ⊓ G₂ :=
      ⟨hA₁ _, by rw [h1]; exact G₂.mul_mem hx (G₂.inv_mem (hA₂ _))⟩
    rw [hdisj, mem_bot] at h2
    have h3 : d.ι₁ (d.π₁ x) = 1 := (injective_iff_map_eq_one E).1 hE _ h2
    conv_lhs => rw [d.decomp x]
    rw [h3, one_mul]
  refine ⟨hinj, hrange₁, ?_⟩
  intro P Q φ
  constructor
  · -- A morphism of `F₁` gives the morphism `(φ, 1)` of `F`, which is a conjugation in `G`.
    intro hφ
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
    have hψ : ψ ∈ F.hom P' Q' := (hprod P' Q' ψ).2 ⟨φ₁, hφ₁, 1, hφ₂, fun x => ⟨by
        show d.π₁ (d.ι₁ (φ (r x) : S₁)) = (φ (inclusion hle _) : S₁)
        rw [d.π₁ι₁]; rfl, by
        show d.π₂ (d.ι₁ (φ (r x) : S₁)) = _
        rw [d.π₂ι₁]; rfl⟩⟩
    obtain ⟨g, hg⟩ := (hR P' Q' ψ).1 hψ
    refine ⟨π g, fun x => ?_⟩
    have hx := hg ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩
    have hrx : r ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩ = x := Subtype.ext (d.π₁ι₁ x)
    have : (ψ ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩ : S) = d.ι₁ (φ x) := by
      show d.ι₁ (φ (r _) : S₁) = _; rw [hrx]
    rw [this] at hx
    show π (E (d.ι₁ (φ x))) = π g * π (E (d.ι₁ x)) * (π g)⁻¹
    rw [hx]; simp only [map_mul, map_inv]
  · -- A conjugation in `G / G₂` lifts to one carrying `E(P × 1)` into `E(Q × S₂)`.
    rintro ⟨gbar, hgbar⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective G₂ gbar
    let Qs : Subgroup S := Q.map d.ι₁ ⊔ d.ι₂.range
    have hQs : IsPGroup 2 (Qs.map E) := (hS.to_subgroup Qs).map E
    have hPs : IsPGroup 2 ((P.map d.ι₁).map E) := (hS.to_subgroup _).map E
    have hQsT : Qs.map E ≤ T := by rintro _ ⟨x, -, rfl⟩; exact hET x
    have hinf : Qs.map E ⊓ G₂ = (T : Subgroup G) ⊓ G₂ := by
      refine le_antisymm (inf_le_inf_right _ hQsT) (le_inf ?_ inf_le_right)
      rintro y ⟨hyT, hy⟩
      rw [← hrange] at hyT
      obtain ⟨x, rfl⟩ := hyT
      refine ⟨x, ?_, rfl⟩
      rw [hTG₂ x hy]
      exact mem_sup_right ⟨_, rfl⟩
    have hidx : ¬ 2 ∣ (Qs.map E).relIndex G₂ := by
      rw [← inf_relIndex_right, hinf, inf_relIndex_right, ← relIndex_sup_normal]
      exact fun h => T.not_dvd_index (h.trans (relIndex_dvd_index_of_le le_sup_left))
    obtain ⟨g', hg', hconj⟩ := exists_lift G₂ hQs hPs hidx g (by
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨E (d.ι₁ (φ ⟨p, hp⟩)), mem_map_of_mem _ (mem_sup_left (mem_map_of_mem _ (φ _).2)), ?_⟩
      have := hgbar ⟨p, hp⟩
      show π (g * E (d.ι₁ p) * g⁻¹) = π (E (d.ι₁ (φ ⟨p, hp⟩)))
      rw [map_mul, map_mul, map_inv]
      exact this.symm)
    obtain ⟨ψ, hψ, hψe⟩ := hR.exists_mem (P := P.map d.ι₁) (Q := Qs) hE g'
      (fun x => hconj _ (mem_map_of_mem _ x.2))
    obtain ⟨φ₁, hφ₁, φ₂, -, hx⟩ := (hprod _ _ ψ).1 hψ
    have hle : P ≤ (P.map d.ι₁).map d.π₁ := fun p hp => ⟨d.ι₁ p, mem_map_of_mem _ hp, d.π₁ι₁ p⟩
    have hQle : Qs.map d.π₁ ≤ Q := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ ((Q.map d.ι₁ ⊔ d.ι₂.range : Subgroup S) : Set S) := hx
      haveI := d.range_ι₂_normal
      rw [mul_normal] at hx'
      obtain ⟨_, ⟨q, hq, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := hx'
      rw [map_mul, d.π₁ι₁, d.π₁ι₂, mul_one]; exact hq
    -- `φ` agrees with the first component `φ₁` of `ψ`.
    refine F₁.mem_of_eq_on hφ₁ hle φ (fun x => ?_)
    have h1 := (hx ⟨d.ι₁ x, mem_map_of_mem _ x.2⟩).1
    have h2 : (⟨d.π₁ (d.ι₁ x), mem_map_of_mem _ (mem_map_of_mem _ x.2)⟩ : (P.map d.ι₁).map d.π₁) =
        ⟨x, hle x.2⟩ := Subtype.ext (d.π₁ι₁ x)
    rw [h2] at h1
    rw [← h1]
    apply hinj
    show π (E (d.ι₁ (φ x))) = π (E (d.ι₁ (d.π₁ (ψ _))))
    rw [← hπE, hψe]
    have := hgbar x
    show π (E (d.ι₁ (φ x))) = π (g' * E (d.ι₁ x) * g'⁻¹)
    rw [map_mul, map_mul, map_inv, show π g' = π g from hg']
    exact this

/-- **Factor lemma.** If `F = F₁ × F₂` has no nontrivial normal subgroup and is realized by `G` with
`O(G) = 1`, then `F₁` is realizable. -/
lemma realizable_fst_of_oddCore_eq_bot [GoldschmidtTheoremA] [Finite G] (hS : IsPGroup 2 S)
    (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E) (hE : Function.Injective E)
    (T : Sylow 2 G) (hrange : E.range = T) (hodd : goldschmidtOddCore G = ⊥)
    (hO : ∀ D : Subgroup S, F.IsNormalSubgroup D → D = ⊥) : Realizable 2 F₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, h3⟩ := realizedBy_fst_quot hS hprod hR hE T hrange hodd hO
  exact (realizable_iff 2 F₁).2 ⟨_, inferInstance, inferInstance, _, _, h1, h2, h3⟩

end Core

end AndersenOliverVentura
