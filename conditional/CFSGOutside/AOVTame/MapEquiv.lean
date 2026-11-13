import CFSGOutside.AOVTame.Linking

/-!
# AOV tameness: functoriality of `L^c_S(G)` under group isomorphisms

A group isomorphism `e : G ≃* G'` with `e(S) = S'` induces an isomorphism of categories
`L^c_S(G) → L^c_{S'}(G')`, `P ↦ e(P)`, `[g] ↦ [e(g)]`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u v

variable {G : Type u} [Group G] {G' : Type v} [Group G']

lemma map_conjSub (e : G ≃* G') (g : G) (P : Subgroup G) :
    (conjSub g P).map e.toMonoidHom = conjSub (e g) (P.map e.toMonoidHom) := by
  ext y
  simp only [mem_map_equiv, mem_conjSub, map_mul, map_inv, MulEquiv.symm_apply_apply]

lemma map_centralizer (e : G ≃* G') (P : Subgroup G) :
    (centralizer (P : Set G)).map e.toMonoidHom = centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  simp only [mem_map_equiv, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h x hx
    have := h _ hx
    apply e.symm.injective
    simpa using this
  · intro h x hx
    have := h (e x) (by simpa using hx)
    apply e.injective
    simpa using this

lemma isCentric_map (e : G ≃* G') {S P : Subgroup G} (h : IsCentric S P) :
    IsCentric (S.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  refine ⟨map_mono h.1, fun g hg => ?_⟩
  have key : conjSub g (P.map e.toMonoidHom) = (conjSub (e.symm g) P).map e.toMonoidHom := by
    rw [map_conjSub, MulEquiv.apply_symm_apply]
  rw [key] at hg ⊢
  have hg' : conjSub (e.symm g) P ≤ S :=
    (map_le_map_iff_of_injective e.injective).1 hg
  have h2 := congrArg (Subgroup.map e.toMonoidHom) (h.2 _ hg')
  rw [map_inf_eq _ _ _ e.injective, map_inf_eq _ _ _ e.injective, map_centralizer] at h2
  exact h2

lemma mem_transporter_map (e : G ≃* G') {P Q : Subgroup G} {g : G} (hg : g ∈ transporter P Q) :
    e g ∈ transporter (P.map e.toMonoidHom) (Q.map e.toMonoidHom) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨g * x * g⁻¹, hg x hx, by simp⟩

variable (p : ℕ) [Fact p.Prime]

lemma map_opCent_le (e : G ≃* G') (P : Subgroup G) :
    (opCent p P).map e.toMonoidHom ≤ opCent p (P.map e.toMonoidHom) := by
  let f : centralizer (P : Set G) →* centralizer ((P.map e.toMonoidHom : Subgroup G') : Set G') :=
    { toFun := fun c => ⟨e c, by rw [← map_centralizer]; exact mem_map_of_mem _ c.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp only [coe_mul, map_mul] }
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  exact ⟨f c, map_oP_le p f ⟨c, hc, rfl⟩, rfl⟩

/-- `[g] ↦ [e(g)]`. -/
def Mor.map (e : G ≃* G') {P Q : Subgroup G} (φ : Mor p P Q) :
    Mor p (P.map e.toMonoidHom) (Q.map e.toMonoidHom) :=
  Quotient.liftOn φ (fun g => mk p (e g) (mem_transporter_map e g.2)) (by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ (hgh : g⁻¹ * h ∈ _)
    apply (mk_eq_mk p).2
    have := map_opCent_le p e P (mem_map_of_mem _ hgh)
    simpa using this)

@[simp] lemma Mor.map_mk (e : G ≃* G') {P Q : Subgroup G} (g : G) (hg : g ∈ transporter P Q) :
    Mor.map p e (mk p g hg) = mk p (e g) (mem_transporter_map e hg) := rfl

lemma mk_heq {P P' Q Q' : Subgroup G} (hP : P = P') (hQ : Q = Q') {g g' : G} (h : g = g')
    (hx : g ∈ transporter P Q) (hx' : g' ∈ transporter P' Q') :
    HEq (mk p g hx) (mk p g' hx') := by
  subst hP hQ h; rfl

variable {S : Subgroup G} {S' : Subgroup G'}

/-- The functor `L^c_S(G) → L^c_{S'}(G')` induced by `e : G ≃* G'` with `e(S) = S'`. -/
def mapFunctor (e : G ≃* G') (hS : S.map e.toMonoidHom = S') : Obj p S ⥤ Obj p S' where
  obj P := ⟨P.1.map e.toMonoidHom, hS ▸ isCentric_map e P.2⟩
  map φ := Mor.map p e φ
  map_id P := by
    show Mor.map p e (mk p 1 _) = mk p 1 _
    simp only [Mor.map_mk, map_one]
  map_comp := by
    rintro P Q R ⟨⟨g, hg⟩⟩ ⟨⟨h, hh⟩⟩
    show Mor.map p e (comp p (mk p h hh) (mk p g hg)) =
      comp p (Mor.map p e (mk p h hh)) (Mor.map p e (mk p g hg))
    simp only [comp_mk, Mor.map_mk, map_mul]

@[simp] lemma mapFunctor_obj (e : G ≃* G') (hS : S.map e.toMonoidHom = S') (P : Obj p S) :
    ((mapFunctor p e hS).obj P).1 = P.1.map e.toMonoidHom := rfl

lemma mapFunctor_map_mk (e : G ≃* G') (hS : S.map e.toMonoidHom = S') {P Q : Obj p S} (g : G)
    (hg : g ∈ transporter P.1 Q.1) :
    (mapFunctor p e hS).map (show P ⟶ Q from mk p g hg) = mk p (e g) (mem_transporter_map e hg) :=
  rfl

lemma map_map_equiv {G'' : Type*} [Group G''] (e : G ≃* G') (e' : G' ≃* G'') (P : Subgroup G) :
    (P.map e.toMonoidHom).map e'.toMonoidHom = P.map (e.trans e').toMonoidHom := by
  rw [map_map]; rfl

lemma map_refl (P : Subgroup G) : P.map (MulEquiv.refl G).toMonoidHom = P := by
  ext x; simp [mem_map_equiv]

lemma mapFunctor_comp {G'' : Type v} [Group G''] {S'' : Subgroup G''} (e : G ≃* G')
    (e' : G' ≃* G'') (hS : S.map e.toMonoidHom = S') (hS' : S'.map e'.toMonoidHom = S'') :
    mapFunctor p e hS ⋙ mapFunctor p e' hS' =
      mapFunctor p (e.trans e') (by rw [← map_map_equiv, hS, hS']) := by
  apply Functor.hext (fun X => Obj.ext (map_map_equiv e e' X.1))
  rintro X Y ⟨⟨g, hg⟩⟩
  exact mk_heq p (map_map_equiv e e' X.1) (map_map_equiv e e' Y.1) rfl _ _

lemma mapFunctor_refl (hS : S.map (MulEquiv.refl G).toMonoidHom = S) :
    mapFunctor p (MulEquiv.refl G) hS = 𝟭 (Obj p S) := by
  apply Functor.hext (fun X => Obj.ext (map_refl X.1))
  rintro X Y ⟨⟨g, hg⟩⟩
  exact mk_heq p (map_refl X.1) (map_refl Y.1) rfl _ _

lemma map_symm_map (e : G ≃* G') (hS : S.map e.toMonoidHom = S') :
    S'.map e.symm.toMonoidHom = S := by
  rw [← hS, map_map_equiv, MulEquiv.self_trans_symm, map_refl]

lemma mapFunctor_congr {e e' : G ≃* G'} (h : e = e') (hS : S.map e.toMonoidHom = S')
    (hS' : S.map e'.toMonoidHom = S') : mapFunctor p e hS = mapFunctor p e' hS' := by
  subst h; rfl

/-- The isomorphism `L^c_S(G) ≅ L^c_{S'}(G')` induced by `e : G ≃* G'` with `e(S) = S'`. -/
def mapIso {G' : Type u} [Group G'] {S' : Subgroup G'} (e : G ≃* G')
    (hS : S.map e.toMonoidHom = S') : Cat.of (Obj p S) ≅ Cat.of (Obj p S') where
  hom := (mapFunctor p e hS).toCatHom
  inv := (mapFunctor p e.symm (map_symm_map e hS)).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change mapFunctor p e hS ⋙ mapFunctor p e.symm (map_symm_map e hS) = 𝟭 _
    rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.self_trans_symm e) _ (map_refl S),
      mapFunctor_refl]
  inv_hom_id := by
    apply Cat.ext
    change mapFunctor p e.symm (map_symm_map e hS) ⋙ mapFunctor p e hS = 𝟭 _
    rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.symm_trans_self e) _ (map_refl S'),
      mapFunctor_refl]

@[simp] lemma mapIso_fn {G' : Type u} [Group G'] {S' : Subgroup G'} (e : G ≃* G')
    (hS : S.map e.toMonoidHom = S') : (mapIso p e hS).hom.toFunctor = mapFunctor p e hS := rfl

end AndersenOliverVentura.Tame
