import CFSGOutside.AOVTame.OutTyp

/-!
# AOV tameness: `κ_G : Out(G) → Out_typ(L^c_S(G))` and tame fusion systems
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T : Sylow p G)

lemma exists_map_eq_conjSub (α : MulAut G) :
    ∃ g : G, (T : Subgroup G).map α.toMonoidHom = conjSub g T := by
  let T' : Sylow p G := T.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
  refine ⟨g, ?_⟩
  have h1 : ((g • T : Sylow p G) : Subgroup G) = (T' : Subgroup G) := by rw [hg]
  have h2 : (T' : Subgroup G) = (T : Subgroup G).map α.toMonoidHom := Sylow.coe_mapSurjective _ _
  rw [Sylow.coe_subgroup_smul, h2] at h1
  rw [← h1]
  ext x
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_conjSub]
  simp [MulAut.smul_def]

lemma conj_inv_mul_mem (α : MulAut G) {g : G}
    (hg : (T : Subgroup G).map α.toMonoidHom = conjSub g T) :
    (T : Subgroup G).map ((MulAut.conj g)⁻¹ * α).toMonoidHom = T := by
  change (T : Subgroup G).map (α.trans (MulAut.conj g)⁻¹).toMonoidHom = T
  rw [← map_map_equiv, hg, conjSub, map_map_equiv]
  rw [show (MulAut.conj g).trans (MulAut.conj g)⁻¹ = MulEquiv.refl G by
    ext x; simp only [MulEquiv.trans_apply, MulAut.conj_apply, MulAut.inv_def,
      MulAut.conj_symm_apply, MulEquiv.refl_apply]; group, map_refl]

/-- `κ` on `Aut(G)`: write `α = c_g ∘ β` with `β ∈ Aut(G,S)` and take the class of `β`. -/
noncomputable def kappaAut (α : MulAut G) : OutTyp p (T : Subgroup G) :=
  kappaElt p ((MulAut.conj (exists_map_eq_conjSub p T α).choose)⁻¹ * α)
    (conj_inv_mul_mem p T α (exists_map_eq_conjSub p T α).choose_spec)

lemma kappaAut_eq (α : MulAut G) (g : G)
    (hg : (T : Subgroup G).map α.toMonoidHom = conjSub g T) :
    kappaAut p T α = kappaElt p ((MulAut.conj g)⁻¹ * α) (conj_inv_mul_mem p T α hg) := by
  set g₀ := (exists_map_eq_conjSub p T α).choose
  have hg₀ := (exists_map_eq_conjSub p T α).choose_spec
  have hn : (T : Subgroup G).map (MulAut.conj (g⁻¹ * g₀)).toMonoidHom = T := by
    have h1 : conjSub g (T : Subgroup G) = conjSub g₀ T := hg.symm.trans hg₀
    change conjSub (g⁻¹ * g₀) (T : Subgroup G) = T
    rw [← conjSub_conjSub, ← h1, conjSub_conjSub, inv_mul_cancel]
    ext x; simp [mem_conjSub]
  have he : (MulAut.conj g)⁻¹ * α = MulAut.conj (g⁻¹ * g₀) * ((MulAut.conj g₀)⁻¹ * α) := by
    ext x; simp [mul_assoc]
  have h2 : (T : Subgroup G).map (MulAut.conj (g⁻¹ * g₀) * ((MulAut.conj g₀)⁻¹ * α)).toMonoidHom
      = T := by rw [← he]; exact conj_inv_mul_mem p T α hg
  rw [kappaElt_congr p he _ h2, kappaElt_conj_mul p _ hn _ (conj_inv_mul_mem p T α hg₀)]
  rfl

lemma kappaAut_mul (α α' : MulAut G) : kappaAut p T (α * α') = kappaAut p T α * kappaAut p T α' := by
  obtain ⟨g, hg⟩ := exists_map_eq_conjSub p T α
  obtain ⟨g', hg'⟩ := exists_map_eq_conjSub p T α'
  have hh : (T : Subgroup G).map (α * α').toMonoidHom = conjSub (α g' * g) T := by
    change (T : Subgroup G).map (α'.trans α).toMonoidHom = _
    rw [← map_map_equiv, hg', map_conjSub, hg, conjSub_conjSub]
  rw [kappaAut_eq p T _ _ hh, kappaAut_eq p T _ _ hg, kappaAut_eq p T _ _ hg']
  have he : (MulAut.conj (α g' * g))⁻¹ * (α * α') =
      ((MulAut.conj g)⁻¹ * α) * ((MulAut.conj g')⁻¹ * α') := by
    ext x; simp [mul_assoc]
  rw [kappaElt_congr p he _ (by rw [← he]; exact conj_inv_mul_mem p T _ hh)]
  exact kappaElt_mul p _ _ _ _ _

lemma kappaAut_conj (x : G) : kappaAut p T (MulAut.conj x) = 1 := by
  rw [kappaAut_eq p T _ x rfl]
  rw [kappaElt_congr p (inv_mul_cancel (MulAut.conj x)) _ (map_refl _)]
  exact kappaElt_one p _

/-- `κ` on `Aut(G)` as a monoid homomorphism. -/
noncomputable def kappaAutHom : MulAut G →* OutTyp p (T : Subgroup G) where
  toFun := kappaAut p T
  map_one' := by
    rw [show (1 : MulAut G) = MulAut.conj 1 by ext; simp]; exact kappaAut_conj p T 1
  map_mul' := kappaAut_mul p T

/-- `κ_G : Out(G) → Out_typ(L^c_S(G))` (AOV §2.2). -/
noncomputable def kappa : Out G →* OutTyp p (T : Subgroup G) :=
  QuotientGroup.lift _ (kappaAutHom p T) (by
    rintro _ ⟨x, rfl⟩
    exact kappaAut_conj p T x)

/-- For `β ∈ Aut(G,S)`, `κ_G[β]` is the class of `P ↦ β(P)`, `[g] ↦ [β(g)]`. -/
lemma kappa_mk (β : MulAut G) (hβ : (T : Subgroup G).map β.toMonoidHom = T) :
    kappa p T (QuotientGroup.mk β) = kappaElt p β hβ := by
  rw [kappa, QuotientGroup.lift_mk]
  change kappaAut p T β = _
  rw [kappaAut_eq p T β 1 (by rw [hβ]; ext x; simp [mem_conjSub])]
  exact kappaElt_congr p (by simp) _ _

end AndersenOliverVentura.Tame
