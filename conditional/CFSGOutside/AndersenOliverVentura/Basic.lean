import CFSGOutside.AndersenOliverVentura.Defs

/-!
# Andersen–Oliver–Ventura: basic facts about fusion systems and realizations

`RealizedBy F E` says that the injective homomorphism `E : S → G` identifies `F` with the fusion
system of `G` over `E(S)`; `realizable_iff` rephrases `Realizable` with it.
-/

namespace AndersenOliverVentura

open Subgroup

universe u v

variable {S : Type u} [Group S]

namespace FusionSystem

variable (F : FusionSystem S)

lemma inclusion_mem {P Q : Subgroup S} (h : P ≤ Q) : inclusion h ∈ F.hom P Q :=
  F.conj_mem _ 1 fun x => by simp

/-- A morphism of `F` restricted to `P' ≤ P` and corestricted to any `Q'` containing its image is
a morphism of `F`. -/
lemma mem_of_eq_on {P Q P' Q' : Subgroup S} {φ : P →* Q} (hφ : φ ∈ F.hom P Q) (hle : P' ≤ P)
    (φ' : P' →* Q') (h : ∀ x : P', (φ' x : S) = φ ⟨x, hle x.2⟩) : φ' ∈ F.hom P' Q' := by
  have h0 : φ.comp (inclusion hle) ∈ F.hom P' Q := F.comp_mem hφ (F.inclusion_mem hle)
  obtain ⟨R, -, ψ, hψ, χ, -, -, hψχ, hφψ⟩ := F.factor h0
  have hRQ : R ≤ Q' := by
    intro r hr
    have h1 : ψ (χ ⟨r, hr⟩) = ⟨r, hr⟩ := by rw [← MonoidHom.comp_apply, hψχ]; rfl
    have h2 := hφψ (χ ⟨r, hr⟩)
    rw [h1] at h2
    have h3 := h (χ ⟨r, hr⟩)
    simp only [MonoidHom.comp_apply] at h2
    have : (r : S) = φ' (χ ⟨r, hr⟩) := by rw [h3]; exact h2.symm.trans rfl
    rw [this]; exact (φ' _).2
  have he : φ' = (inclusion hRQ).comp ψ := by
    ext x
    simp only [MonoidHom.comp_apply, coe_inclusion]
    rw [h x, ← hφψ x]; rfl
  rw [he]
  exact F.comp_mem (F.inclusion_mem hRQ) hψ

end FusionSystem

/-- `E : S → G` realizes `F`: `φ ∈ Hom_F(P,Q)` iff `E ∘ φ` is conjugation by some `g ∈ G` on `E(P)`. -/
def RealizedBy (F : FusionSystem S) {G : Type v} [Group G] (E : S →* G) : Prop :=
  ∀ (P Q : Subgroup S) (φ : P →* Q), φ ∈ F.hom P Q ↔ ∃ g : G, ∀ x : P, E (φ x) = g * E x * g⁻¹

/-- Conjugation by `g` as a homomorphism `P' → Q'` of subgroups of `T ≤ G`. -/
def conjMap {G : Type v} [Group G] {T : Subgroup G} (P' Q' : Subgroup T) (g : G)
    (h : ∀ y : P', g * ((y : T) : G) * g⁻¹ ∈ Q'.map T.subtype) : P' →* Q' :=
  MonoidHom.mk' (fun y => ⟨⟨g * ((y : T) : G) * g⁻¹, by
      obtain ⟨q, -, hq⟩ := h y; rw [← hq]; exact q.2⟩, by
      obtain ⟨q, hqQ, hq⟩ := h y
      have : q = ⟨g * ((y : T) : G) * g⁻¹, by rw [← hq]; exact q.2⟩ := Subtype.ext hq
      rw [← this]; exact hqQ⟩)
    (fun a b => by apply Subtype.ext; apply Subtype.ext; simp only [MulMemClass.coe_mul]; group)

@[simp] lemma coe_conjMap {G : Type v} [Group G] {T : Subgroup G} (P' Q' : Subgroup T) (g : G)
    (h : ∀ y : P', g * ((y : T) : G) * g⁻¹ ∈ Q'.map T.subtype) (y : P') :
    ((conjMap P' Q' g h y : T) : G) = g * ((y : T) : G) * g⁻¹ := rfl

/-- Through an isomorphism `e : S ≃* T`, the morphisms of `F_T(G)` are the conjugations. -/
lemma iso_ofGroup_iff {G : Type v} [Group G] {T : Subgroup G} (e : S ≃* T) (P Q : Subgroup S)
    (φ : P →* Q) :
    (∃ ψ ∈ (ofGroup G T).hom (P.map e.toMonoidHom) (Q.map e.toMonoidHom),
      ∀ x : P, (ψ ⟨e x, mem_map_of_mem _ x.2⟩ : T) = e (φ x)) ↔
    ∃ g : G, ∀ x : P, ((e (φ x) : T) : G) = g * ((e x : T) : G) * g⁻¹ := by
  constructor
  · rintro ⟨ψ, ⟨g, hg⟩, hψ⟩
    exact ⟨g, fun x => by rw [← hψ x, hg]⟩
  · rintro ⟨g, hg⟩
    have h : ∀ y : P.map e.toMonoidHom, g * ((y : T) : G) * g⁻¹ ∈
        (Q.map e.toMonoidHom).map T.subtype := by
      rintro ⟨_, x, hx, rfl⟩
      refine ⟨e (φ ⟨x, hx⟩), mem_map_of_mem _ (φ ⟨x, hx⟩).2, ?_⟩
      simp only [coe_subtype]
      rw [hg ⟨x, hx⟩]; rfl
    exact ⟨conjMap _ _ g h, ⟨g, fun y => rfl⟩, fun x => Subtype.ext (by
      simp only [coe_conjMap]; rw [hg x])⟩

lemma realizable_iff (p : ℕ) (F : FusionSystem S) :
    Realizable p F ↔ ∃ (G : Type) (_ : Group G) (_ : Finite G) (T : Sylow p G) (E : S →* G),
      Function.Injective E ∧ E.range = T ∧ RealizedBy F E := by
  constructor
  · rintro ⟨G, _, _, T, ⟨f⟩⟩
    refine ⟨G, inferInstance, inferInstance, T, (T : Subgroup G).subtype.comp f.toMulEquiv.toMonoidHom,
      (T : Subgroup G).subtype_injective.comp f.toMulEquiv.injective, ?_, ?_⟩
    · ext y
      constructor
      · rintro ⟨x, rfl⟩; exact (f.toMulEquiv x).2
      · intro hy; exact ⟨f.toMulEquiv.symm ⟨y, hy⟩, by simp⟩
    · intro P Q φ
      rw [f.hom_iff, iso_ofGroup_iff]
      rfl
  · rintro ⟨G, _, _, T, E, hE, hrange, hR⟩
    let e : S ≃* (T : Subgroup G) := (MonoidHom.ofInjective hE).trans (MulEquiv.subgroupCongr hrange)
    have he : ∀ x, ((e x : (T : Subgroup G)) : G) = E x := fun x => by
      change ((MonoidHom.ofInjective hE x : E.range) : G) = E x
      rw [MonoidHom.ofInjective_apply]
    refine ⟨G, inferInstance, inferInstance, T, ⟨⟨e, fun P Q φ => ?_⟩⟩⟩
    rw [iso_ofGroup_iff, hR]
    simp only [he]

/-- A conjugation `c_g` carrying `E(P)` into `E(Q)` is (the image under `E` of) a morphism of a
fusion system realized by `E`. -/
lemma RealizedBy.exists_mem {F : FusionSystem S} {G : Type v} [Group G] {E : S →* G}
    (hR : RealizedBy F E) (hE : Function.Injective E) {P Q : Subgroup S} (g : G)
    (h : ∀ x : P, g * E x * g⁻¹ ∈ Q.map E) :
    ∃ φ ∈ F.hom P Q, ∀ x : P, E (φ x) = g * E x * g⁻¹ := by
  let c : P →* Q.map E := MonoidHom.mk' (fun x => ⟨g * E x * g⁻¹, h x⟩)
    (fun a b => by apply Subtype.ext; simp only [MulMemClass.coe_mul, map_mul]; group)
  let φ : P →* Q := (equivMapOfInjective Q E hE).symm.toMonoidHom.comp c
  have hφ : ∀ x : P, E (φ x) = g * E x * g⁻¹ := fun x => by
    have h1 := coe_equivMapOfInjective_apply Q E hE (φ x)
    have h2 : equivMapOfInjective Q E hE (φ x) = c x := by
      simp [φ]
    rw [h2] at h1
    exact h1.symm
  exact ⟨φ, (hR P Q φ).2 ⟨g, hφ⟩, hφ⟩

end AndersenOliverVentura
