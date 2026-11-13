import CFSGOutside.AndersenOliverVentura.Basic

/-!
# AOV tameness: the fusion system realized by an injective homomorphism

For an injective `E : S → G`, the morphisms `P → Q` are the maps `x ↦ E⁻¹(g E(x) g⁻¹)`; this is
`F_{E(S)}(G)` transported to `S`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup

variable {S : Type*} [Group S] {G : Type*} [Group G]

/-- The fusion system on `S` realized by an injective `E : S → G`. -/
def ofHom (E : S →* G) (hE : Function.Injective E) : FusionSystem S where
  hom P Q := {φ | ∃ g : G, ∀ x : P, E (φ x) = g * E x * g⁻¹}
  conj_mem := by
    intro P Q φ s h
    exact ⟨E s, fun x => by rw [h x]; simp⟩
  injective := by
    rintro P Q φ ⟨g, hg⟩ x y hxy
    have h1 := hg x
    rw [hxy, hg y] at h1
    exact Subtype.ext (hE (by simpa using h1.symm))
  comp_mem := by
    rintro P Q R ψ φ ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, fun x => by simp only [MonoidHom.comp_apply, hg, hh]; group⟩
  factor := by
    rintro P Q φ ⟨g, hg⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 := hg x
      rw [hxy, hg y] at h1
      exact Subtype.ext (hE (by simpa using h1.symm))
    refine ⟨img φ, img_le φ, (equivImg hφ).toMonoidHom, ⟨g, fun x => ?_⟩,
      (equivImg hφ).symm.toMonoidHom, ⟨g⁻¹, fun y => ?_⟩, ?_, ?_, fun x => ?_⟩
    · simp [hg x]
    · have h := hg ((equivImg hφ).symm y)
      have hy : ((equivImg hφ ((equivImg hφ).symm y) : img φ) : S) = (y : S) := by simp
      rw [coe_equivImg] at hy
      rw [hy] at h
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, inv_inv]
      rw [h]; group
    · ext x; simp
    · ext x; simp
    · simp

lemma realizedBy_ofHom (E : S →* G) (hE : Function.Injective E) : RealizedBy (ofHom E hE) E :=
  fun _ _ _ => Iff.rfl

end AndersenOliverVentura.Tame
