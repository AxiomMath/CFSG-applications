import CFSGOutside.AOVTame.WreathKer

/-!
# AOV tameness: components are multiplicative; product automorphisms; the class-level kernel
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {H : Type} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

lemma lautA_congr {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {SA : Sylow p A}
    {SB : Sylow p B} {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (h : α = α') (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') : lautA SB hα hf = lautA SB hα' hf' := by subst h; rfl

section Mul
variable {α α' : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα' : α' ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}

lemma betaPi_mul_aut {x : ι → H} (hx : x ∈ piSub ι S) :
    betaPi (mul_mem hα hα') x hx = betaPi hα (betaPi hα' x hx) (betaFun hα' ⟨x, hx⟩).2 := by
  have := betaFun_mul_aut hα hα' ⟨x, hx⟩
  exact congrArg Subtype.val this

lemma betaPi_mem (hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)))
    {x : ι → H} (hx : x ∈ piSub ι S) : betaPi hα x hx ∈ piSub ι S := (betaFun hα ⟨x, hx⟩).2

lemma CoordPres.mul (hc : CoordPres hα) (hc' : CoordPres hα') : CoordPres (mul_mem hα hα') := by
  intro i x hx
  obtain ⟨y, hy⟩ := hc' i x hx
  have hyS : y ∈ (S : Subgroup H) := by
    have := (mem_piSub ι S).1 (betaPi_mem hα' (mulSingle_mem_piSub (i := i) hx)) i
    rw [hy] at this; simpa using this
  obtain ⟨z, hz⟩ := hc i y hyS
  refine ⟨z, ?_⟩
  rw [betaPi_mul_aut (hα := hα) (hα' := hα')]
  exact (betaPi_congr hα hy _ (mulSingle_mem_piSub hyS)).trans hz

lemma coordComp_mul (hc : CoordPres hα) (hc' : CoordPres hα') (i : ι) :
    coordComp (hc.mul hc') i = coordComp hc i * coordComp hc' i := by
  unfold coordComp
  rw [← lautA_mul (coordAut_mem hα i) (CoordPres.presFactors hc i) (coordAut_mem hα' i)
    (CoordPres.presFactors hc' i)]
  exact lautA_congr (conjIso_mul _ _ α α') _ _ _ _


end Mul

section MapAut

lemma conjIso_mapAut {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] (e : G ≃* G')
    {T : Sylow p G} {T' : Sylow p G'} (hT : (T : Subgroup G).map e.toMonoidHom = T')
    (β : MulAut G) (hβ : (T : Subgroup G).map β.toMonoidHom = T) :
    conjIso e hT (mapAut p β hβ) = mapAut p (e.symm.trans (β.trans e)) (by
      rw [← map_map_equiv, map_symm_map e hT, ← map_map_equiv, hβ, hT]) := by
  apply LAut.ext_fn
  rw [conjIso_fn, mapAut_fn, mapAut_fn, mapFunctor_comp, mapFunctor_comp]

/-- `∏ γ_j`. -/
def piAut (γ : ι → MulAut H) : MulAut (ι → H) := MulEquiv.piCongrRight γ

lemma piAut_apply (γ : ι → MulAut H) (g : ι → H) (j : ι) : piAut γ g j = γ j (g j) := rfl

variable (γ : ι → MulAut H) (hγ : ∀ j, (S : Subgroup H).map (γ j).toMonoidHom = S)
include hγ

lemma map_piAut : ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)).map (piAut γ).toMonoidHom =
    (piSylow ι S : Sylow p (ι → H)) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine (mem_piSub ι S).2 fun j => ?_
    change γ j (g j) ∈ (S : Subgroup H)
    rw [← hγ j]; exact mem_map_of_mem _ ((mem_piSub ι S).1 hg j)
  · intro hg
    refine ⟨(piAut γ).symm g, (mem_piSub ι S).2 fun j => ?_, (piAut γ).apply_symm_apply g⟩
    change (γ j).symm (g j) ∈ (S : Subgroup H)
    have := (mem_piSub ι S).1 hg j
    rw [← hγ j] at this
    obtain ⟨y, hy, e⟩ := this
    have : (γ j).symm (g j) = y := by rw [← e]; exact (γ j).symm_apply_apply y
    rw [this]; exact hy

lemma coordPres_piAut : CoordPres (mapAut_mem p (piAut γ) (map_piAut γ hγ)) := by
  intro i x hx
  refine ⟨γ i x, ?_⟩
  unfold betaPi
  rw [betaFun_mapIso]
  funext j
  change γ j ((Pi.mulSingle i x : ι → H) j) = (Pi.mulSingle i (γ i x) : ι → H) j
  by_cases hj : j = i
  · subst hj; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, (γ j).map_one]

lemma coordComp_piAut (i : ι) :
    coordComp (coordPres_piAut γ hγ) i = mapAut p (γ i) (hγ i) := by
  have hB : ((piSylow {j // j ≠ i} S : Sylow p ({j // j ≠ i} → H)) : Subgroup _).map
      (piAut (fun j : {j // j ≠ i} => γ j)).toMonoidHom = (piSylow {j // j ≠ i} S : Sylow p _) :=
    map_piAut (fun j : {j // j ≠ i} => γ j) (fun j => hγ j)
  have h1 : coordAut i (mapAut p (piAut γ) (map_piAut γ hγ)) =
      mapAut p (MulEquiv.prodCongr (γ i) (piAut (fun j : {j // j ≠ i} => γ j)))
        (prodCongr_mem (hγ i) hB) := by
    unfold coordAut
    rw [conjIso_mapAut]
    apply LAut.ext_fn
    rw [mapAut_fn, mapAut_fn]
    refine mapFunctor_congr p ?_ _ _
    apply MulEquiv.ext
    intro x
    apply Prod.ext
    · change (piAut γ) ((coordEquiv i).symm x) i = γ i x.1
      rw [piAut_apply, coordEquiv_symm_apply_self]
    · funext j
      change (piAut γ) ((coordEquiv i).symm x) j = γ j (x.2 j)
      rw [piAut_apply, coordEquiv_symm_apply_ne _ _ j.2]
  unfold coordComp
  rw [lautA_congr h1 _ _ (mapAut_mem p _ (prodCongr_mem (hγ i) hB)) (presFactors_mapIso (hγ i) hB)]
  apply LAut.ext_fn
  rw [lautA_fn, mapAut_fn]
  exact fnA_mapIso (hγ i) hB

end MapAut

section Kernel
variable {δ : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hδ : δ ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hδ)

include hc in
lemma CoordPres.inv : CoordPres (inv_mem hδ) := by
  intro i x hx
  -- `y ↦ β(δ)(y)_i` is an injective map `S → S`, hence surjective
  have hcoord : ∀ y (hy : y ∈ (S : Subgroup H)), ∃ y' ∈ (S : Subgroup H),
      betaPi hδ (Pi.mulSingle i y) (mulSingle_mem_piSub hy) = Pi.mulSingle i y' := by
    intro y hy
    obtain ⟨y', hy'⟩ := hc i y hy
    have := (mem_piSub ι S).1 (betaPi_mem hδ (mulSingle_mem_piSub (i := i) hy)) i
    rw [hy'] at this
    exact ⟨y', by simpa using this, hy'⟩
  choose f hfS hf using hcoord
  let F : ↥(S : Subgroup H) → ↥(S : Subgroup H) := fun y => ⟨f y y.2, hfS y y.2⟩
  have hFinj : Function.Injective F := by
    intro a b e
    have e' : f a a.2 = f b b.2 := congrArg Subtype.val e
    have h1 : betaFun hδ ⟨Pi.mulSingle i (a : H), mulSingle_mem_piSub (i := i) a.2⟩ =
        betaFun hδ ⟨Pi.mulSingle i (b : H), mulSingle_mem_piSub (i := i) b.2⟩ := Subtype.ext (by
      change betaPi hδ _ _ = betaPi hδ _ _
      rw [hf a a.2, hf b b.2, e'])
    have h2 := congrArg Subtype.val (betaFun_injective hδ h1)
    have := congrFun h2 i
    simp at this
    exact this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hFinj) ⟨x, hx⟩
  refine ⟨y, ?_⟩
  have e1 : betaPi hδ (Pi.mulSingle i y) (mulSingle_mem_piSub y.2) = Pi.mulSingle i x := by
    rw [hf y y.2]; exact congrArg (Pi.mulSingle i) (congrArg Subtype.val hy)
  have e2 := betaFun_inv_aut hδ ⟨Pi.mulSingle i y, mulSingle_mem_piSub y.2⟩
  have e3 : betaFun hδ ⟨Pi.mulSingle i y, mulSingle_mem_piSub y.2⟩ =
      ⟨Pi.mulSingle i x, mulSingle_mem_piSub hx⟩ := Subtype.ext e1
  rw [e3] at e2
  exact congrArg Subtype.val e2

end Kernel

end AndersenOliverVentura.Tame
