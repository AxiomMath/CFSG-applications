import CFSGOutside.AOVTame.WreathHom

/-!
# AOV tameness: the splitting on coordinate-preserving classes

If `κ_H[γ_i] = [α_i]` for the components of a coordinate-preserving `α`, then
`κ_{ι → H}[∏ γ_i] = [α]`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

lemma autClass_eq_one_iff {G : Type} [Group G] [Finite G] {T : Subgroup G} {α : LAut p T}
    (hα : α ∈ autTypI p T) : autClass hα = 1 ↔ Nonempty (α.fn ≅ 𝟭 _) := by
  rw [autClass, ← map_one ((natIsoCon p T).mk')]
  exact (natIsoCon p T).eq

lemma eq_mapAut_conj_of_class {G : Type} [Group G] [Finite G] {T : Sylow p G}
    {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G)) (h : autClass hα = 1) :
    ∃ (n : G) (hn : (T : Subgroup G).map (MulAut.conj n).toMonoidHom = T),
      α = mapAut p (MulAut.conj n) hn := by
  obtain ⟨ω⟩ := (autClass_eq_one_iff hα).1 h
  obtain ⟨n, hn, e⟩ := eq_conj_of_iso (one_mem _) hα ω.symm
  refine ⟨n, hn, LAut.ext_fn p _ ?_⟩
  rw [e, mapAut_fn]; rfl

lemma piAut_conj (n : ι → H) : piAut (fun j => MulAut.conj (n j)) = MulAut.conj n := by
  ext g j; rfl

lemma conjIso_one {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] (e : G ≃* G')
    {T : Sylow p G} {T' : Sylow p G'} (hT : (T : Subgroup G).map e.toMonoidHom = T') :
    conjIso e hT (1 : LAut p (T : Subgroup G)) = 1 := by
  apply LAut.ext_fn
  rw [conjIso_fn, LAut.fn_one, LAut.fn_one, Functor.id_comp, mapFunctor_comp,
    mapFunctor_congr p (MulEquiv.symm_trans_self e) _ (map_refl _), mapFunctor_refl]

lemma coordPres_one : CoordPres (one_mem (autTypI p ((piSylow ι S : Sylow p (ι → H)) :
    Subgroup (ι → H)))) := by
  intro i x hx
  refine ⟨x, ?_⟩
  unfold betaPi
  rw [betaFun_one_aut]

lemma presFactors_one {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {SA : Sylow p A}
    {SB : Sylow p B} :
    PresFactors (one_mem (autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))) := by
  constructor
  · intro a ha; rw [betaFun_one_aut]
  · intro b hb; rw [betaFun_one_aut]

lemma coordComp_one (i : ι) : coordComp (coordPres_one (ι := ι) (S := S)) i = 1 := by
  unfold coordComp
  exact (lautA_congr (conjIso_one _ _) _ _ (one_mem _) presFactors_one).trans
    (LAut.ext_fn p _ fnA_one)

lemma coordComp_inv {δ : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
    {hδ : δ ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hδ)
    (i : ι) : coordComp (CoordPres.inv hc) i = (coordComp hc i)⁻¹ := by
  have h := coordComp_mul (CoordPres.inv hc) hc i
  have h1 : coordComp ((CoordPres.inv hc).mul hc) i = 1 := by
    rw [← coordComp_one (S := S) i]
    unfold coordComp
    exact lautA_congr (by rw [inv_mul_cancel]) _ _ _ _
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

section
variable {δ : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hδ : δ ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hδ)

/-- **Class-level kernel**: a coordinate-preserving `δ` with inner components is inner. -/
theorem autClass_eq_one_of_comp (h : ∀ i, autClass (coordComp_mem hc i) = 1) : autClass hδ = 1 := by
  choose n hn e using fun i => eq_mapAut_conj_of_class (coordComp_mem hc i) (h i)
  set γ : ι → MulAut H := fun j => MulAut.conj (n j)
  have hγ : ∀ j, (S : Subgroup H).map (γ j).toMonoidHom = S := hn
  have hcc := coordPres_piAut γ hγ
  set c := mapAut p (piAut γ) (map_piAut γ hγ)
  have hc' := (CoordPres.inv hcc).mul hc
  have h1 : ∀ i, coordComp hc' i = 1 := by
    intro i
    rw [coordComp_mul (CoordPres.inv hcc) hc i, coordComp_inv hcc i, coordComp_piAut γ hγ i, e i,
      inv_mul_cancel]
  have h2 := eq_one_of_comp hc' h1
  have h3 : δ = c := (inv_mul_eq_one.1 h2).symm
  have hcmem := mapAut_mem p (piAut γ) (map_piAut γ hγ)
  rw [autClass_congr h3 hδ hcmem]
  have hconj : piAut γ = MulAut.conj n := piAut_conj n
  have hn' : ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)).map (MulAut.conj n).toMonoidHom =
      (piSylow ι S : Sylow p (ι → H)) := by rw [← hconj]; exact map_piAut γ hγ
  rw [autClass_congr (show c = mapAut p (MulAut.conj n) hn' from by
    apply LAut.ext_fn; rw [mapAut_fn, mapAut_fn]; exact mapFunctor_congr p hconj _ _) hcmem
    (mapAut_mem p _ hn')]
  exact autClass_mapIso_conj n hn'

lemma autClass_inv_mul {G : Type} [Group G] [Finite G] {T : Subgroup G} {α : LAut p T}
    (hα : α ∈ autTypI p T) : autClass (inv_mem hα) * autClass hα = 1 := by
  rw [← autClass_mul, autClass_congr (inv_mul_cancel _) _ (one_mem _)]
  exact map_one ((natIsoCon p T).mk')

/-- **`κ` on coordinate-preserving classes.** -/
theorem kappa_piAut (γ : ι → MulAut H) (hγ : ∀ j, (S : Subgroup H).map (γ j).toMonoidHom = S)
    (hk : ∀ i, kappaElt p (γ i) (hγ i) = autClass (coordComp_mem hc i)) :
    kappaElt p (piAut γ) (map_piAut γ hγ) = autClass hδ := by
  have hcc := coordPres_piAut γ hγ
  have hd := (CoordPres.inv hcc).mul hc
  have h1 : ∀ i, autClass (coordComp_mem hd i) = 1 := by
    intro i
    have hmi := mapAut_mem p (γ i) (hγ i)
    have eq : coordComp hd i = (mapAut p (γ i) (hγ i))⁻¹ * coordComp hc i := by
      rw [coordComp_mul (CoordPres.inv hcc) hc i, coordComp_inv hcc i, coordComp_piAut γ hγ i]
    rw [autClass_congr eq (coordComp_mem hd i) (mul_mem (inv_mem hmi) (coordComp_mem hc i)),
      autClass_mul (inv_mem hmi) (coordComp_mem hc i), ← hk i, ← autClass_eq_kappaElt]
    exact autClass_inv_mul hmi
  have h2 := autClass_eq_one_of_comp hd h1
  rw [← autClass_eq_kappaElt]
  have hm := mapAut_mem p (piAut γ) (map_piAut γ hγ)
  have h3 : δ = mapAut p (piAut γ) (map_piAut γ hγ) * ((mapAut p (piAut γ) (map_piAut γ hγ))⁻¹ * δ) := by
    group
  rw [autClass_congr h3 hδ (mul_mem hm (mul_mem (inv_mem hm) hδ)),
    autClass_mul hm (mul_mem (inv_mem hm) hδ)]
  rw [show autClass (mul_mem (inv_mem hm) hδ) = 1 from h2, mul_one]

end

end AndersenOliverVentura.Tame
