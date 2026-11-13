import CFSGOutside.AOVTame.WreathOut

/-!
# AOV tameness: equivariance of the components under permutations
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime]

section General
variable {G G' G'' : Type} [Group G] [Group G'] [Group G''] [Finite G] [Finite G'] [Finite G'']

lemma conjIso_trans (e : G ≃* G') (f : G' ≃* G'') {T : Sylow p G} {T' : Sylow p G'}
    {T'' : Sylow p G''} (hT : (T : Subgroup G).map e.toMonoidHom = T')
    (hT' : (T' : Subgroup G').map f.toMonoidHom = T'') (α : LAut p (T : Subgroup G)) :
    conjIso f hT' (conjIso e hT α) = conjIso (e.trans f) (by rw [← map_map_equiv, hT, hT']) α := by
  apply LAut.ext_fn
  rw [conjIso_fn, conjIso_fn, conjIso_fn]
  have h1 : mapFunctor p f.symm (map_symm_map f hT') ⋙ mapFunctor p e.symm (map_symm_map e hT) =
      mapFunctor p (e.trans f).symm (map_symm_map (e.trans f) (by rw [← map_map_equiv, hT, hT'])) := by
    rw [mapFunctor_comp]; exact mapFunctor_congr p (by ext; rfl) _ _
  have h2 : mapFunctor p e hT ⋙ mapFunctor p f hT' =
      mapFunctor p (e.trans f) (by rw [← map_map_equiv, hT, hT']) := by
    rw [mapFunctor_comp]
  calc (mapFunctor p f.symm (map_symm_map f hT') ⋙ mapFunctor p e.symm (map_symm_map e hT) ⋙
        α.fn ⋙ mapFunctor p e hT) ⋙ mapFunctor p f hT' =
      (mapFunctor p f.symm (map_symm_map f hT') ⋙ mapFunctor p e.symm (map_symm_map e hT)) ⋙
        α.fn ⋙ (mapFunctor p e hT ⋙ mapFunctor p f hT') := rfl
    _ = _ := by rw [h1, h2]

lemma conjIso_congr {e e' : G ≃* G'} (h : e = e') {T : Sylow p G} {T' : Sylow p G'}
    (hT : (T : Subgroup G).map e.toMonoidHom = T') (hT' : (T : Subgroup G).map e'.toMonoidHom = T')
    (α : LAut p (T : Subgroup G)) : conjIso e hT α = conjIso e' hT' α := by subst h; rfl

lemma conjIso_eq_mul (e : MulAut G) {T : Sylow p G} (hT : (T : Subgroup G).map e.toMonoidHom = T)
    (α : LAut p (T : Subgroup G)) :
    conjIso e hT α = mapAut p e hT * α * (mapAut p e hT)⁻¹ := by
  apply LAut.ext_fn
  rw [conjIso_fn, LAut.fn_mul, LAut.fn_mul, mapAut_fn]
  rfl

end General

section Snd
variable {A B B' : Type} [Group A] [Group B] [Group B'] [Finite A] [Finite B] [Finite B']
  {SA : Sylow p A} {SB : Sylow p B} {SB' : Sylow p B'}

lemma prodCongr_mem' {δ : B ≃* B'} (hδ : (SB : Subgroup B).map δ.toMonoidHom = SB') :
    ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map
      (MulEquiv.prodCongr (MulEquiv.refl A) δ).toMonoidHom = (prodSylow SA SB' : Sylow p (A × B')) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, e⟩
    change (x, δ y) = (a, b) at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨hx, by rw [← hδ]; exact mem_map_of_mem _ hy⟩
  · rintro ⟨ha, hb⟩
    rw [← hδ] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨(a, y), ⟨ha, hy⟩, rfl⟩

variable {β : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hβ : β ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hβ) {δ : B ≃* B'} (hδ : (SB : Subgroup B).map δ.toMonoidHom = SB')

include hf in
lemma presFactors_conjSnd :
    PresFactors (conjIso_mem (MulEquiv.prodCongr (MulEquiv.refl A) δ) (prodCongr_mem' (SA := SA) hδ) hβ) := by
  have key : ∀ (a : A) (b : B) (ha : a ∈ (SA : Subgroup A)) (hb : b ∈ (SB : Subgroup B))
      (hb' : δ b ∈ (SB' : Subgroup B')),
      ((betaFun (conjIso_mem (MulEquiv.prodCongr (MulEquiv.refl A) δ) (prodCongr_mem' (SA := SA) hδ) hβ)
        ⟨(a, δ b), mem_prodSylow ha hb'⟩ : _) : A × B') =
        (bA hβ a ha, δ (bB hβ b hb)) := by
    intro a b ha hb hb'
    have := betaFun_conjIso (MulEquiv.prodCongr (MulEquiv.refl A) δ) (prodCongr_mem' (SA := SA) hδ) hβ
      ⟨(a, b), mem_prodSylow ha hb⟩ (mem_prodSylow ha hb')
    refine this.trans ?_
    rw [betaFun_pair hβ hf a ha b hb]; rfl
  constructor
  · intro a ha
    have := key a 1 ha (one_mem _) (by rw [map_one]; exact one_mem _)
    have e : (⟨(a, δ 1), mem_prodSylow ha (by rw [map_one]; exact one_mem _)⟩ :
        ((prodSylow SA SB' : Sylow p (A × B')) : Subgroup (A × B'))) =
        ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ := Subtype.ext (by simp)
    rw [e] at this
    rw [this, bB_one hβ hf, map_one]
  · intro b' hb'
    have hb'' := hb'
    rw [← hδ] at hb''
    obtain ⟨b, hb, e⟩ := hb''
    change δ b = b' at e
    subst e
    have := key 1 b (one_mem _) hb hb'
    rw [this, bA_one hβ hf]

/-- Conjugating by `Id × δ` does not change the first component. -/
theorem lautA_conjSnd :
    lautA SB' (conjIso_mem (MulEquiv.prodCongr (MulEquiv.refl A) δ) (prodCongr_mem' (SA := SA) hδ) hβ)
      (presFactors_conjSnd hβ hf hδ) = lautA SB hβ hf := by
  set ε := MulEquiv.prodCongr (MulEquiv.refl A) δ
  set hε := prodCongr_mem' (SA := SA) hδ
  set β' := conjIso ε hε β
  have hβ' := conjIso_mem ε hε hβ
  have hinvP : ∀ P : Obj p (SA : Subgroup A),
      (mapFunctor p ε.symm (map_symm_map ε hε)).obj (prodObj SB' P) = prodObj SB P := by
    intro P
    apply Obj.ext
    change (P.val.prod (SB' : Subgroup B')).map ε.symm.toMonoidHom = P.val.prod (SB : Subgroup B)
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, e⟩
      change (x, δ.symm y) = (a, b) at e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      refine ⟨hx, ?_⟩
      rw [← hδ] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    · rintro ⟨ha, hb⟩
      refine ⟨(a, δ b), ⟨ha, by rw [← hδ]; exact mem_map_of_mem _ hb⟩, ?_⟩
      change (a, δ.symm (δ b)) = (a, b)
      rw [δ.symm_apply_apply]
  have hfst : ∀ R : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)),
      ((mapFunctor p ε hε).obj R).val.map (MonoidHom.fst A B') = R.val.map (MonoidHom.fst A B) := by
    intro R
    ext a
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨ε x, ⟨x, hx, rfl⟩, rfl⟩
  have hobj : ∀ P, (fnA SB' (α := β')).obj P = (fnA SB (α := β)).obj P := by
    intro P
    apply Obj.ext
    change ((β'.fn.obj (prodObj SB' P)).val).map (MonoidHom.fst A B') =
      ((β.fn.obj (prodObj SB P)).val).map (MonoidHom.fst A B)
    rw [show β'.fn.obj (prodObj SB' P) = (mapFunctor p ε hε).obj
      (β.fn.obj ((mapFunctor p ε.symm (map_symm_map ε hε)).obj (prodObj SB' P))) from rfl, hfst,
      hinvP]
  apply LAut.ext_fn
  rw [lautA_fn, lautA_fn]
  refine Functor.hext hobj ?_
  rintro P Q ⟨⟨g, hg⟩⟩
  change HEq (projFst (β'.fn.map (liftA SB' (show P ⟶ Q from mk p g hg))))
    (projFst (β.fn.map (liftA SB (show P ⟶ Q from mk p g hg))))
  have h1 : HEq ((mapFunctor p ε.symm (map_symm_map ε hε)).map (liftA SB' (show P ⟶ Q from mk p g hg)))
      (liftA SB (show P ⟶ Q from mk p g hg)) := by
    rw [liftA_mk, liftA_mk]
    change HEq (mk p (ε.symm (g, 1)) _) _
    exact mk_heq p (congrArg Obj.val (hinvP P)) (congrArg Obj.val (hinvP Q))
      (by change (g, δ.symm 1) = (g, 1); rw [map_one]) _ _
  have h2 := Functor.map_heq' β.fn (hinvP P) (hinvP Q) h1
  obtain ⟨⟨k, hk⟩, ek⟩ := Quotient.exists_rep (β.fn.map (liftA SB (show P ⟶ Q from mk p g hg)))
  rw [← ek] at h2
  change HEq (projFst ((mapFunctor p ε hε).map (β.fn.map ((mapFunctor p ε.symm
    (map_symm_map ε hε)).map (liftA SB' (show P ⟶ Q from mk p g hg)))))) _
  rw [← ek]
  have h3 := Functor.map_heq' (mapFunctor p ε hε) (congrArg β.fn.obj (hinvP P))
    (congrArg β.fn.obj (hinvP Q)) h2
  have h3' : HEq ((mapFunctor p ε hε).map (β.fn.map ((mapFunctor p ε.symm (map_symm_map ε hε)).map
      (liftA SB' (show P ⟶ Q from mk p g hg)))))
      (show (mapFunctor p ε hε).obj (β.fn.obj (prodObj SB P)) ⟶
        (mapFunctor p ε hε).obj (β.fn.obj (prodObj SB Q)) from
        mk p (ε k) (mem_transporter_map ε hk)) := h3
  clear h3
  refine (projFst_heq (congrArg Obj.val (congrArg (mapFunctor p ε hε).obj (congrArg β.fn.obj (hinvP P))))
    (congrArg Obj.val (congrArg (mapFunctor p ε hε).obj (congrArg β.fn.obj (hinvP Q)))) h3').trans ?_
  change HEq (mk p (ε k).1 (mem_transporter_fst (mem_transporter_map ε hk)))
    (mk p k.1 (mem_transporter_fst hk))
  exact mk_heq p (hfst _) (hfst _) rfl _ _

end Snd

end AndersenOliverVentura.Tame

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

variable {p : ℕ} [hp : Fact p.Prime]
variable {H : Type} [Group H] [Finite H] {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sylow p H}

section Perm
variable (σ : Equiv.Perm ι) (k : ι)

/-- `σ` restricted to complements: `H^{ι∖σ⁻¹k} ≃ H^{ι∖k}`. -/
def permCompl : ({j // j ≠ σ.symm k} → H) ≃* ({j // j ≠ k} → H) where
  toFun r j := r ⟨σ.symm j, fun h => j.2 (σ.symm.injective h)⟩
  invFun r j := r ⟨σ j, fun h => j.2 (σ.injective (by rw [h, Equiv.apply_symm_apply]))⟩
  left_inv r := by funext j; simp
  right_inv r := by funext j; simp
  map_mul' r r' := rfl

lemma map_permCompl :
    ((piSylow {j // j ≠ σ.symm k} S : Sylow p _) : Subgroup ({j // j ≠ σ.symm k} → H)).map
      (permCompl (H := H) σ k).toMonoidHom = (piSylow {j // j ≠ k} S : Sylow p _) := by
  ext r
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_piSub _ S).2 fun j => (mem_piSub _ S).1 hr _
  · intro hr
    refine ⟨(permCompl σ k).symm r, (mem_piSub _ S).2 fun j => (mem_piSub _ S).1 hr _, ?_⟩
    exact (permCompl σ k).apply_symm_apply r

lemma permEquiv_trans_coord :
    (permEquiv σ).trans (coordEquiv k) =
      (coordEquiv (σ.symm k)).trans (MulEquiv.prodCongr (MulEquiv.refl H) (permCompl σ k)) := by
  apply MulEquiv.ext
  intro g
  rfl

end Perm

section CoordPerm
variable {α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))}
  {hα : α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))} (hc : CoordPres hα)
  (σ : Equiv.Perm ι)

lemma permEquiv_mulSingle (i : ι) (x : H) :
    permEquiv σ (Pi.mulSingle i x) = Pi.mulSingle (σ i) x := by
  funext j
  rw [permEquiv_apply]
  by_cases hj : j = σ i
  · subst hj; simp
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne]
    intro h; apply hj; rw [← h]; simp

/-- `σ̂ α σ̂⁻¹`. -/
noncomputable def permConj (α : LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H))) :
    LAut p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  conjIso (permEquiv σ) (map_permEquiv_piSylow σ S) α

include hα in
lemma permConj_mem : permConj σ α ∈ autTypI p ((piSylow ι S : Sylow p (ι → H)) : Subgroup (ι → H)) :=
  conjIso_mem _ _ hα

lemma permEquiv_mem_piSub {x : ι → H} (hx : x ∈ piSub ι S) : permEquiv σ x ∈ piSub ι S :=
  (mem_piSub ι S).2 fun j => (mem_piSub ι S).1 hx _

include hα in
lemma betaPi_permConj {x : ι → H} (hx : x ∈ piSub ι S) :
    betaPi (permConj_mem (hα := hα) σ) (permEquiv σ x) (permEquiv_mem_piSub σ hx) =
      permEquiv σ (betaPi hα x hx) := by
  have := betaFun_conjIso (permEquiv σ) (map_permEquiv_piSylow σ S) hα ⟨x, hx⟩
    (permEquiv_mem_piSub σ hx)
  exact this

include hc in
lemma CoordPres.perm : CoordPres (permConj_mem (hα := hα) σ) := by
  intro i x hx
  obtain ⟨y, hy⟩ := hc (σ.symm i) x hx
  refine ⟨y, ?_⟩
  have hx' := mulSingle_mem_piSub (ι := ι) (i := σ.symm i) hx
  have h1 : Pi.mulSingle i x = permEquiv σ (Pi.mulSingle (σ.symm i) x) := by
    rw [permEquiv_mulSingle]; simp
  rw [betaPi_congr _ h1 _ (permEquiv_mem_piSub σ hx'), betaPi_permConj (hα := hα) σ hx', hy,
    permEquiv_mulSingle]
  simp

include hc in
/-- **Equivariance**: `(σ̂ α σ̂⁻¹)_k = α_{σ⁻¹ k}`. -/
theorem coordComp_perm (k : ι) :
    coordComp (CoordPres.perm hc σ) k = coordComp hc (σ.symm k) := by
  unfold coordComp
  have h1 : coordAut k (permConj σ α) =
      conjIso (MulEquiv.prodCongr (MulEquiv.refl H) (permCompl σ k))
        (prodCongr_mem' (SA := S) (map_permCompl σ k)) (coordAut (σ.symm k) α) := by
    unfold coordAut permConj
    rw [conjIso_trans, conjIso_trans]
    exact conjIso_congr (permEquiv_trans_coord σ k) _ _ α
  rw [lautA_congr h1 (coordAut_mem (permConj_mem (hα := hα) σ) k)
    (CoordPres.presFactors (CoordPres.perm hc σ) k)
    (conjIso_mem _ _ (coordAut_mem hα (σ.symm k)))
    (presFactors_conjSnd (coordAut_mem hα (σ.symm k)) (CoordPres.presFactors hc (σ.symm k))
      (map_permCompl σ k))]
  exact lautA_conjSnd (coordAut_mem hα (σ.symm k)) (CoordPres.presFactors hc (σ.symm k))
    (map_permCompl σ k)

end CoordPerm

end AndersenOliverVentura.Tame
