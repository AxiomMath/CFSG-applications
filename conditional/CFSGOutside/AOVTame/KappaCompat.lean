import CFSGOutside.AOVTame.Induced
import CFSGOutside.AOVTame.Kappa

/-!
# AOV tameness: compatibility of `κ` with induced isomorphisms of linking systems
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {H K : Type u} [Group H] [Group K] [Finite H] [Finite K] {p : ℕ} [Fact p.Prime]
  {SH : Sylow p H} {SK : Sylow p K} {f : H →* K}

namespace FusionHom

variable (hf : FusionHom p SH SK f)
include hf

lemma mapFunctor_fwd (β : MulAut H) (hβ : (SH : Subgroup H).map β.toMonoidHom = SH)
    (β' : MulAut K) (hβ' : (SK : Subgroup K).map β'.toMonoidHom = SK)
    (hc : ∀ x, f (β x) = β' (f x)) :
    mapFunctor p β hβ ⋙ hf.fwd = hf.fwd ⋙ mapFunctor p β' hβ' := by
  have hobj : ∀ P : Subgroup H, (P.map β.toMonoidHom).map f = (P.map f).map β'.toMonoidHom := by
    intro P
    rw [map_map, map_map]
    congr 1
    ext x; exact hc x
  apply Functor.hext (fun P => Obj.ext (hobj P.val))
  rintro P Q ⟨⟨h, hh⟩⟩
  exact mk_heq p (hobj P.val) (hobj Q.val) (hc h) _ _

lemma outTyp_kappaElt (β : MulAut H) (hβ : (SH : Subgroup H).map β.toMonoidHom = SH)
    (β' : MulAut K) (hβ' : (SK : Subgroup K).map β'.toMonoidHom = SK)
    (hc : ∀ x, f (β x) = β' (f x)) :
    hf.typIso.outTyp (kappaElt p β hβ) = kappaElt p β' hβ' := by
  rw [kappaElt, TypIso.outTyp_mk, kappaElt]
  congr 1
  apply Subtype.ext
  apply Cat.ext
  change hf.bwd ⋙ mapFunctor p β hβ ⋙ hf.fwd = mapFunctor p β' hβ'
  rw [hf.mapFunctor_fwd β hβ β' hβ' hc, ← Functor.assoc, hf.bwd_fwd]
  rfl

end FusionHom

end AndersenOliverVentura.Tame
