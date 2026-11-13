import CFSGOutside.AOVTame.Product
import CFSGOutside.AOVTame.Induced
import CFSGOutside.AOVTame.Kappa

/-!
# AOV tameness: auxiliary lemmas for the splitting of `κ` on a factor

* products of centric subgroups are centric;
* any homomorphism carries `O^p(C(P))` into `O^p(C(f P))`;
* conjugating an element of `Aut_typ^I` by an induced isomorphism of linking systems;
* `P ↦ β(P)` lies in `Aut_typ^I`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

section Prod
variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]

lemma conjSub_prod (g : A × B) (P : Subgroup A) (Q : Subgroup B) :
    conjSub g (P.prod Q) = (conjSub g.1 P).prod (conjSub g.2 Q) := by
  ext ⟨a, b⟩
  simp only [mem_conjSub, mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

lemma mem_centralizer_prod' {P : Subgroup A} {Q : Subgroup B} {c : A × B} :
    c ∈ centralizer ((P.prod Q : Subgroup (A × B)) : Set (A × B)) ↔
      c.1 ∈ centralizer (P : Set A) ∧ c.2 ∈ centralizer (Q : Set B) := by
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · exact congrArg Prod.fst (h (x, 1) ⟨hx, one_mem _⟩)
    · exact congrArg Prod.snd (h (1, y) ⟨one_mem _, hy⟩)
  · rintro ⟨h1, h2⟩ x hx
    exact Prod.ext (h1 _ hx.1) (h2 _ hx.2)

/-- A product of centric subgroups is centric. -/
lemma isCentric_prod {SA : Subgroup A} {SB : Subgroup B} {P : Subgroup A} {Q : Subgroup B}
    (hP : IsCentric SA P) (hQ : IsCentric SB Q) : IsCentric (SA.prod SB) (P.prod Q) := by
  refine ⟨prod_mono hP.1 hQ.1, fun g hg => ?_⟩
  rw [conjSub_prod] at hg ⊢
  have hg₁ : conjSub g.1 P ≤ SA := fun y hy =>
    (hg (show ((y, 1) : A × B) ∈ (conjSub g.1 P).prod (conjSub g.2 Q) from ⟨hy, one_mem _⟩)).1
  have hg₂ : conjSub g.2 Q ≤ SB := fun y hy =>
    (hg (show ((1, y) : A × B) ∈ (conjSub g.1 P).prod (conjSub g.2 Q) from ⟨one_mem _, hy⟩)).2
  have e₁ := hP.2 g.1 hg₁
  have e₂ := hQ.2 g.2 hg₂
  ext c
  rw [mem_inf, mem_inf, mem_centralizer_prod', mem_prod, mem_prod]
  constructor
  · rintro ⟨⟨c₁, c₂⟩, s₁, s₂⟩
    have m₁ : c.1 ∈ centralizer (conjSub g.1 P : Set A) ⊓ SA := mem_inf.2 ⟨c₁, s₁⟩
    have m₂ : c.2 ∈ centralizer (conjSub g.2 Q : Set B) ⊓ SB := mem_inf.2 ⟨c₂, s₂⟩
    rw [e₁] at m₁; rw [e₂] at m₂
    exact ⟨⟨(mem_inf.1 m₁).1, (mem_inf.1 m₂).1⟩, (mem_inf.1 m₁).2, (mem_inf.1 m₂).2⟩
  · rintro ⟨⟨p₁, p₂⟩, c₁, c₂⟩
    exact ⟨⟨c₁, c₂⟩, hg₁ p₁, hg₂ p₂⟩

end Prod

section Hom
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- Any homomorphism carries `O^p(C_G(P))` into `O^p(C_H(f P))`. -/
lemma map_opCent_le_hom (f : G →* H) (P : Subgroup G) :
    (opCent p P).map f ≤ opCent p (P.map f) := by
  let g : centralizer (P : Set G) →* centralizer ((P.map f : Subgroup H) : Set H) :=
    { toFun := fun c => ⟨f (c : G), by
        rw [mem_centralizer_iff]
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul, (mem_centralizer_iff.1 c.2 x hx)]⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp; rfl }
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨g c, map_oP_le p g ⟨c, hc, rfl⟩, rfl⟩

end Hom

section Map
variable {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] {S : Subgroup G}

lemma preservesIncl_mapFunctor (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    PreservesIncl p S (mapFunctor p β hβ) := fun P Q h =>
  ⟨map_mono h, by
    change Mor.map p β (mk p 1 _) = mk p 1 _
    rw [Mor.map_mk]; exact mk_congr p (map_one β) _ _⟩

lemma mapIso_mem (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    (mapIso p β hβ : LAut p S) ∈ autTypI p S :=
  ⟨isIsotypical_mapFunctor p β hβ, preservesIncl_mapFunctor p β hβ⟩

end Map

namespace FusionHom

variable {H K : Type u} [Group H] [Group K] [Finite H] [Finite K] {p : ℕ} [Fact p.Prime]
  {SH : Sylow p H} {SK : Sylow p K} {f : H →* K} (hf : FusionHom p SH SK f)
include hf

lemma fwd_map_incl {P Q : Obj p (SH : Subgroup H)} (h : P.1 ≤ Q.1) :
    hf.fwd.map (incl p _ h) = incl p _ (map_mono h : (hf.fwd.obj P).1 ≤ (hf.fwd.obj Q).1) := by
  change hf.fwdMor (Tame.mk p 1 _) = Tame.mk p 1 _
  rw [fwdMor_mk]; exact mk_congr p (map_one f) _ _

lemma bwd_map_incl {P Q : Obj p (SK : Subgroup K)} (h : P.1 ≤ Q.1) :
    hf.bwd.map (incl p _ h) =
      incl p _ (inf_le_inf_right _ (comap_mono h) : (hf.bwd.obj P).1 ≤ (hf.bwd.obj Q).1) := by
  exact hf.liftMor_mk (hf.map_comap_inf P.2.1).symm (hf.map_comap_inf Q.2.1).symm
    ((hf.isCentric_map_iff inf_le_right).2 ((hf.map_comap_inf P.2.1).symm ▸ P.2)) inf_le_right _ _
    (by simp [one_mem])

/-- Transport of an automorphism of `L^c_{SH}(H)` to `L^c_{SK}(K)` along `f`. -/
noncomputable def conjAut (α : LAut p (SH : Subgroup H)) : LAut p (SK : Subgroup K) :=
  hf.iso.symm ≪≫ α ≪≫ hf.iso

lemma conjAut_fn (α : LAut p (SH : Subgroup H)) : (hf.conjAut α).fn = hf.bwd ⋙ α.fn ⋙ hf.fwd :=
  rfl

lemma conjAut_mem {α : LAut p (SH : Subgroup H)} (hα : α ∈ autTypI p (SH : Subgroup H)) :
    hf.conjAut α ∈ autTypI p (SK : Subgroup K) := by
  refine ⟨?_, fun P Q h => ?_⟩
  · rw [conjAut_fn]
    exact (hf.typIso.inv.comp p ((isIsotypical_iff_isoTyp p _).1 hα.1)).comp p hf.typIso.hom
  · rw [conjAut_fn]
    obtain ⟨h₁, e₁⟩ := hα.2 (hf.bwd.obj P) (hf.bwd.obj Q) (inf_le_inf_right _ (comap_mono h) :
      (hf.bwd.obj P).1 ≤ (hf.bwd.obj Q).1)
    refine ⟨map_mono h₁, ?_⟩
    change hf.fwd.map (α.fn.map (hf.bwd.map (incl p _ h))) = _
    rw [hf.bwd_map_incl, e₁, hf.fwd_map_incl]

end FusionHom

end AndersenOliverVentura.Tame
