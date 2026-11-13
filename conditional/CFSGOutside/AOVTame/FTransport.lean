import CFSGOutside.AOVTame.FIso
import CFSGOutside.AOVTame.Perm

/-!
# AOV tameness: transporting direct factors along isomorphisms of fusion systems

An isomorphism `F_T(G) ≅ F_{T'}(G')` carries strongly closed subgroups, direct decompositions and
minimal direct factors of `T` to those of `T'`, and restricts to isomorphisms
`F_X(G) ≅ F_{X'}(G')`. The automorphism `β` induced by `α ∈ Aut_typ^I(L)` is such an isomorphism.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

section Emap
variable {G G' G'' : Type*} [Group G] [Group G'] [Group G''] {T : Subgroup G} {T' : Subgroup G'}
  {T'' : Subgroup G''}

/-- The image of `X ≤ G` under `e : T ≃* T'` (of `X ∩ T`). -/
def emap (e : T ≃* T') (X : Subgroup G) : Subgroup G' :=
  ((X.subgroupOf T).map e.toMonoidHom).map T'.subtype

variable {e : T ≃* T'}

lemma mem_emap {X : Subgroup G} {y : G'} : y ∈ emap e X ↔ ∃ x : T, (x : G) ∈ X ∧ y = e x := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

lemma emap_le (X : Subgroup G) : emap e X ≤ T' := by
  rintro _ ⟨y, -, rfl⟩; exact y.2

lemma emap_mono {X Y : Subgroup G} (h : X ≤ Y) : emap e X ≤ emap e Y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_emap.1 hy
  exact mem_emap.2 ⟨x, h hx, rfl⟩

lemma emap_symm_emap {X : Subgroup G} (hX : X ≤ T) : emap e.symm (emap e X) = X := by
  ext y
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := mem_emap.1 h
    obtain ⟨x, hx, hzx⟩ := mem_emap.1 hz
    have : z = e x := Subtype.ext hzx
    rw [this, MulEquiv.symm_apply_apply]; exact hx
  · intro hy
    exact mem_emap.2 ⟨e ⟨y, hX hy⟩, mem_emap.2 ⟨⟨y, hX hy⟩, hy, rfl⟩, by simp⟩

lemma emap_emap_symm {X : Subgroup G'} (hX : X ≤ T') : emap e (emap e.symm X) = X := by
  have := emap_symm_emap (e := e.symm) hX
  rwa [MulEquiv.symm_symm] at this

lemma emap_bot : emap e ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_emap.1 hy
  have : x = 1 := Subtype.ext hx
  rw [this, map_one]; exact one_mem _

lemma emap_inf (X Y : Subgroup G) : emap e (X ⊓ Y) = emap e X ⊓ emap e Y := by
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_emap.1 h
    exact ⟨mem_emap.2 ⟨x, hx.1, rfl⟩, mem_emap.2 ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, rfl⟩ := mem_emap.1 h1
    obtain ⟨x', hx', e'⟩ := mem_emap.1 h2
    have : x = x' := e.injective (Subtype.ext e')
    subst this
    exact mem_emap.2 ⟨x, ⟨hx, hx'⟩, rfl⟩

lemma mem_emap_self (x : T) {X : Subgroup G} (hx : (x : G) ∈ X) : ((e x : T') : G') ∈ emap e X :=
  mem_emap.2 ⟨x, hx, rfl⟩

end Emap

lemma realizedBy_subtype' {G : Type*} [Group G] (K : Subgroup G) :
    RealizedBy (ofGroup G K) K.subtype :=
  fun _ _ _ => Iff.rfl

@[simp] lemma _root_.AndersenOliverVentura.FusionIso.symm_toMulEquiv {S S' : Type*} [Group S] [Group S'] {F : FusionSystem S}
    {F' : FusionSystem S'} (f : FusionIso F F') : f.symm.toMulEquiv = f.toMulEquiv.symm := rfl

@[simp] lemma _root_.AndersenOliverVentura.FusionIso.trans_toMulEquiv {S S' S'' : Type*} [Group S] [Group S'] [Group S'']
    {F : FusionSystem S} {F' : FusionSystem S'} {F'' : FusionSystem S''} (f : FusionIso F F')
    (f' : FusionIso F' F'') : (f.trans f').toMulEquiv = f.toMulEquiv.trans f'.toMulEquiv := rfl

section Closed
variable {G G' : Type*} [Group G] [Group G'] {T : Subgroup G} {T' : Subgroup G'}

/-- An isomorphism `F_T(G) ≅ F_{T'}(G')` preserves strong closure. -/
lemma fusionStronglyClosed_emap (f : FusionIso (ofGroup G T) (ofGroup G' T')) {X : Subgroup G}
    (hX : fusionStronglyClosed (X : Set G) T) :
    fusionStronglyClosed (emap f.toMulEquiv X : Set G') T' := by
  intro y hy g' hg'
  obtain ⟨x, hxX, rfl⟩ := mem_emap.1 hy
  set e := f.toMulEquiv
  let Q' : Subgroup T' := zpowers (e x)
  have h : ∀ z : Q', g'⁻¹ * ((z : T') : G') * g'⁻¹⁻¹ ∈ (⊤ : Subgroup T').map T'.subtype := by
    rintro ⟨z, hz⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
    subst hk
    have mem : g'⁻¹ * (((e x) ^ k : T') : G') * g'⁻¹⁻¹ ∈ T' := by
      have : g'⁻¹ * (((e x) ^ k : T') : G') * g'⁻¹⁻¹ = (g'⁻¹ * ((e x : T') : G') * g') ^ k := by
        rw [SubgroupClass.coe_zpow]
        have := conj_zpow (a := g'⁻¹) (b := ((e x : T') : G')) (i := k)
        rw [inv_inv] at this ⊢
        exact this.symm
      rw [this]
      exact zpow_mem hg' k
    exact ⟨⟨_, mem⟩, trivial, rfl⟩
  let ψ := conjMap Q' ⊤ g'⁻¹ h
  have hψ : ψ ∈ (ofGroup G' T').hom Q' ⊤ := ⟨g'⁻¹, fun z => rfl⟩
  obtain ⟨φ, ⟨g, hg⟩, hφψ⟩ := (f.symm.hom_iff Q' ⊤ ψ).1 hψ
  set z : Q' := ⟨e x, mem_zpowers _⟩
  have key := (congrArg Subtype.val (hφψ z)).symm.trans
    (hg ⟨f.symm.toMulEquiv z, mem_map_of_mem _ z.2⟩)
  have hv : ((e.symm (ψ z : T') : T) : G) = g * x * g⁻¹ := by
    simp only [FusionIso.symm_toMulEquiv] at key
    rw [key]
    simp [z, e]
  have hmem : ((e.symm (ψ z : T') : T) : G) ∈ X := by
    rw [hv]
    have := hX x hxX g⁻¹ (by rw [inv_inv, ← hv]; exact (e.symm _).2)
    simpa using this
  refine mem_emap.2 ⟨e.symm (ψ z), hmem, ?_⟩
  rw [MulEquiv.apply_symm_apply]
  simp [ψ, z]

end Closed

section Factors
variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {T : Sylow 2 G}
  {T' : Sylow 2 G'} (f : FusionIso (ofGroup G (T : Subgroup G)) (ofGroup G' (T' : Subgroup G')))
include f

lemma Decomp.emap {X Y : Subgroup G} (h : Decomp T X Y) :
    Decomp T' (emap f.toMulEquiv X) (emap f.toMulEquiv Y) where
  leX := emap_le _
  leY := emap_le _
  inf := by rw [← emap_inf, h.inf, emap_bot]
  comm := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_emap.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_emap.1 hb
    have : x * y = y * x := Subtype.ext (h.comm _ hx _ hy)
    have := congrArg (fun z => ((f.toMulEquiv z : (T' : Subgroup G')) : G')) this
    simpa using this
  sup := by
    intro t ht
    obtain ⟨x, hx, y, hy, e⟩ := h.sup _ (f.toMulEquiv.symm ⟨t, ht⟩).2
    refine ⟨_, mem_emap_self (e := f.toMulEquiv) ⟨x, h.leX hx⟩ hx, _,
      mem_emap_self (e := f.toMulEquiv) ⟨y, h.leY hy⟩ hy, ?_⟩
    have h1 : f.toMulEquiv.symm ⟨t, ht⟩ = ⟨x, h.leX hx⟩ * ⟨y, h.leY hy⟩ := Subtype.ext e
    have := congrArg (fun z => ((f.toMulEquiv z : (T' : Subgroup G')) : G')) h1
    simp only [MulEquiv.apply_symm_apply, map_mul, MulMemClass.coe_mul] at this
    exact this
  scX := fusionStronglyClosed_emap f h.scX
  scY := fusionStronglyClosed_emap f h.scY

lemma IsFactor.emap {X : Subgroup G} (h : IsFactor T X) : IsFactor T' (emap f.toMulEquiv X) :=
  let ⟨_, hY⟩ := h; ⟨_, hY.emap f⟩

/-- Minimal direct factors correspond under an isomorphism of fusion systems. -/
lemma IsMinFactor.emap {X : Subgroup G} (h : IsMinFactor T X) :
    IsMinFactor T' (emap f.toMulEquiv X) := by
  obtain ⟨hf, hne, hmin⟩ := h
  have hXT : X ≤ T := let ⟨_, hY⟩ := hf; hY.leX
  refine ⟨hf.emap f, fun he => hne ?_, fun X' hX' hle => ?_⟩
  · have := emap_symm_emap (e := f.toMulEquiv) hXT
    rw [he, emap_bot] at this
    exact this.symm
  · have hX'T : X' ≤ T' := let ⟨_, hY⟩ := hX'; hY.leX
    have h1 := hX'.emap f.symm
    rw [FusionIso.symm_toMulEquiv] at h1
    have h2 : Tame.emap f.toMulEquiv.symm X' ≤ X := by
      rw [← emap_symm_emap (e := f.toMulEquiv) hXT]; exact emap_mono hle
    rcases hmin _ h1 h2 with h3 | h3
    · left
      rw [← emap_emap_symm (e := f.toMulEquiv) hX'T, h3, emap_bot]
    · right
      rw [← emap_emap_symm (e := f.toMulEquiv) hX'T, h3]

end Factors

section Restrict
variable {G G' : Type*} [Group G] [Group G'] {T : Subgroup G} {T' : Subgroup G'}

/-- An isomorphism `F_T(G) ≅ F_{T'}(G')` restricts to `F_X(G) ≅ F_{X'}(G')`. -/
lemma fusionIso_restrict (f : FusionIso (ofGroup G T) (ofGroup G' T')) {X : Subgroup G}
    (hXT : X ≤ T) : Nonempty (FusionIso (ofGroup G X) (ofGroup G' (emap f.toMulEquiv X))) := by
  have hinj : Function.Injective (T'.subtype.comp f.toMulEquiv.toMonoidHom) :=
    T'.subtype_injective.comp f.toMulEquiv.injective
  have hR := realizedBy_comp f T'.subtype_injective (realizedBy_subtype' T')
  have hR' := realizedBy_restrict hXT hinj hR
  refine fusionIso_of_realizedBy (hinj.comp (inclusion_injective hXT)) ?_ hR'
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact mem_emap.2 ⟨inclusion hXT x, x.2, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_emap.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩

end Restrict

section Beta
variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}

/-- `β ∈ Aut(T)` induced by `α ∈ Aut_typ^I(L)` is an automorphism of `F_T(G)` (AOV Lemma 1.15). -/
noncomputable def betaIso [AlperinFusion] {α : LAut p (T : Subgroup G)}
    (hα : α ∈ autTypI p (T : Subgroup G)) :
    FusionIso (ofGroup G (T : Subgroup G)) (ofGroup G (T : Subgroup G)) where
  toMulEquiv := beta hα
  hom_iff P Q φ := by
    constructor
    · rintro ⟨g, hg⟩
      have hP : P.map (T : Subgroup G).subtype ≤ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
      have hPg : (P.map (T : Subgroup G).subtype).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ T := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simp only [inv_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        change g * (x : G) * g⁻¹ ∈ (T : Subgroup G)
        rw [← hg ⟨x, hx⟩]; exact (φ ⟨x, hx⟩ : T).2
      obtain ⟨h, hh⟩ := beta_fusion hα hP hPg
      have key : ∀ x : P, ((beta hα (φ x) : T) : G) = h⁻¹ * ((beta hα x : T) : G) * h⁻¹⁻¹ := by
        intro x
        have e1 := hh x ⟨x, x.2, rfl⟩ (by rw [inv_inv, ← hg x]; exact (φ x : T).2)
        rw [inv_inv]
        have e2 : ((φ x : T) : G) = g⁻¹⁻¹ * ((x : T) : G) * g⁻¹ := by rw [inv_inv]; exact hg x
        change betaG hα ((φ x : T) : G) (φ x : T).2 = _
        have e3 : betaG hα ((φ x : T) : G) (φ x : T).2 =
            betaG hα (g⁻¹⁻¹ * ((x : T) : G) * g⁻¹) (by rw [← e2]; exact (φ x : T).2) := by
          congr 1
        rw [e3, e1]; rfl
      have hmem : ∀ y : P.map (beta hα).toMonoidHom, h⁻¹ * ((y : T) : G) * h⁻¹⁻¹ ∈
          (Q.map (beta hα).toMonoidHom).map (T : Subgroup G).subtype := by
        rintro ⟨_, x, hx, rfl⟩
        refine ⟨beta hα (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, ?_⟩
        rw [coe_subtype, key ⟨x, hx⟩]; rfl
      exact ⟨conjMap _ _ h⁻¹ hmem, ⟨h⁻¹, fun y => rfl⟩, fun x => Subtype.ext (by
        rw [coe_conjMap, key x])⟩
    · rintro ⟨ψ, ⟨g', hg'⟩, hψ⟩
      set P' : Subgroup G := (P.map (beta hα).toMonoidHom).map (T : Subgroup G).subtype
      have hP' : P' ≤ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
      have hval : ∀ x : P, ((beta hα (φ x) : T) : G) = g' * ((beta hα x : T) : G) * g'⁻¹ := by
        intro x
        rw [← hψ x, hg']
      have hPg : P'.map (MulAut.conj g'⁻¹⁻¹).toMonoidHom ≤ T := by
        rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
        simp only [inv_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        have := hval ⟨x, hx⟩
        change g' * ((beta hα x : T) : G) * g'⁻¹ ∈ (T : Subgroup G)
        rw [← this]; exact (beta hα _).2
      obtain ⟨h, hh⟩ := beta_fusion (inv_mem hα) hP' hPg
      refine ⟨h⁻¹, fun x => ?_⟩
      have hb : ((beta hα x : T) : G) ∈ P' := ⟨beta hα x, mem_map_of_mem _ x.2, rfl⟩
      have e1 := hh _ hb (by rw [inv_inv, ← hval x]; exact (beta hα _).2)
      have e2 : betaG (inv_mem hα) (g'⁻¹⁻¹ * ((beta hα x : T) : G) * g'⁻¹)
          (by rw [inv_inv, ← hval x]; exact (beta hα _).2) = ((φ x : T) : G) := by
        have : (⟨g'⁻¹⁻¹ * ((beta hα x : T) : G) * g'⁻¹, by
            rw [inv_inv, ← hval x]; exact (beta hα _).2⟩ : (T : Subgroup G)) = beta hα (φ x) :=
          Subtype.ext (by
            show g'⁻¹⁻¹ * ((beta hα x : T) : G) * g'⁻¹ = _
            rw [inv_inv, hval x])
        unfold betaG
        rw [this]
        exact congrArg Subtype.val (betaFun_inv_aut hα (φ x))
      have e3 : betaG (inv_mem hα) ((beta hα x : T) : G) (hP' hb) = ((x : T) : G) :=
        congrArg Subtype.val (betaFun_inv_aut hα x)
      rw [← e2, e1, e3, inv_inv]

end Beta

end AndersenOliverVentura.Tame
