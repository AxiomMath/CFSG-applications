import CFSGOutside.AndersenOliverVentura.Basic

/-!
# AOV tameness: isomorphisms with `F_T(G)` versus realizations `E : S → G`
-/

namespace AndersenOliverVentura.Tame

open Subgroup

universe u v

variable {S : Type u} [Group S] {F : FusionSystem S} {G : Type v} [Group G]

lemma fusionIso_of_realizedBy {T : Subgroup G} {E : S →* G} (hE : Function.Injective E)
    (hrange : E.range = T) (hR : RealizedBy F E) : Nonempty (FusionIso F (ofGroup G T)) := by
  let e : S ≃* T := (MonoidHom.ofInjective hE).trans (MulEquiv.subgroupCongr hrange)
  have he : ∀ x, ((e x : T) : G) = E x := fun x => by
    change ((MonoidHom.ofInjective hE x : E.range) : G) = E x
    rw [MonoidHom.ofInjective_apply]
  refine ⟨⟨e, fun P Q φ => ?_⟩⟩
  rw [iso_ofGroup_iff, hR]
  simp only [he]

lemma realizedBy_of_fusionIso {T : Subgroup G} (f : FusionIso F (ofGroup G T)) :
    Function.Injective (T.subtype.comp f.toMulEquiv.toMonoidHom) ∧
      (T.subtype.comp f.toMulEquiv.toMonoidHom).range = T ∧
      RealizedBy F (T.subtype.comp f.toMulEquiv.toMonoidHom) := by
  refine ⟨T.subtype_injective.comp f.toMulEquiv.injective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩; exact (f.toMulEquiv x).2
    · intro hy; exact ⟨f.toMulEquiv.symm ⟨y, hy⟩, by simp⟩
  · intro P Q φ
    rw [f.hom_iff, iso_ofGroup_iff]
    rfl

end AndersenOliverVentura.Tame
