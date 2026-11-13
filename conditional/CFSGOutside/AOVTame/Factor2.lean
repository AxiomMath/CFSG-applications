import CFSGOutside.AndersenOliverVentura.Factor

/-!
# Andersen–Oliver–Ventura factor lemma, with the group-level hypothesis `O₂(G) = 1`

Variants of `normalClosure_inf_eq_bot` and `realizedBy_fst_quot` (`Factor.lean`) where the hypothesis
"`F` has no nontrivial normal subgroup" is replaced by "`G` has no nontrivial normal 2-subgroup",
which is all their proofs use (the former implies the latter via `isNormalSubgroup_comap`).
-/

namespace AndersenOliverVentura

open Subgroup CFSGOutside.Corpus
open scoped commutatorElement

universe u v w

variable {S : Type u} {S₁ : Type v} {S₂ : Type w} [Group S] [Group S₁] [Group S₂]

section Core

variable {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}
  {d : ProdData S S₁ S₂} {G : Type} [Group G] {E : S →* G}

/-- The normal closures of the images of `S₁` and `S₂` commute and meet trivially. -/
lemma normalClosure_inf_eq_bot' [GoldschmidtTheoremA] [Finite G] (hS : IsPGroup 2 S)
    (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E) (hE : Function.Injective E)
    (T : Sylow 2 G) (hrange : E.range = T) (hodd : goldschmidtOddCore G = ⊥)
    (hO2 : ∀ D : Subgroup G, D.Normal → IsPGroup 2 D → D = ⊥) :
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
  exact hO2 D inferInstance hDp

/-- **Factor lemma.** If `F = F₁ × F₂` has no nontrivial normal subgroup and is realized by `G` with
`O(G) = 1`, then `G / G₂` realizes `F₁`, where `G₂` is the normal closure of the image of `S₂`. -/
lemma realizedBy_fst_quot' [GoldschmidtTheoremA] [Finite G] (hS : IsPGroup 2 S)
    (hprod : IsProdVia F F₁ F₂ d) (hR : RealizedBy F E) (hE : Function.Injective E)
    (T : Sylow 2 G) (hrange : E.range = T) (hodd : goldschmidtOddCore G = ⊥)
    (hO2 : ∀ D : Subgroup G, D.Normal → IsPGroup 2 D → D = ⊥) :
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
  obtain ⟨hcomm, hdisj⟩ := normalClosure_inf_eq_bot' hS hprod hR hE T hrange hodd hO2
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

end Core

lemma oTwo_of_normal {F : FusionSystem S} {G : Type} [Group G] [Finite G] {E : S →* G}
    (hR : RealizedBy F E) (hE : Function.Injective E) (T : Sylow 2 G) (hrange : E.range = T)
    (hO : ∀ D : Subgroup S, F.IsNormalSubgroup D → D = ⊥) :
    ∀ D : Subgroup G, D.Normal → IsPGroup 2 D → D = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro D hD hDp
  have hDT : D ≤ T := hDp.le_sylow_of_normal T
  have hDc := hO _ (isNormalSubgroup_comap hR hE hrange hDT)
  rw [eq_bot_iff]
  intro y hy
  have : y ∈ E.range := by rw [hrange]; exact hDT hy
  obtain ⟨z, rfl⟩ := this
  have hz : z ∈ D.comap E := hy
  rw [hDc, mem_bot] at hz
  rw [hz, map_one]; exact one_mem _

end AndersenOliverVentura
