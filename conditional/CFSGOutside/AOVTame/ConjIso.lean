import CFSGOutside.AOVTame.AutI
import CFSGOutside.AOVTame.Transport
import CFSGOutside.AOVTame.SplitAux
import CFSGOutside.AOVTame.PhiHom

/-!
# AOV tameness: transporting `Aut_typ^I` along a group isomorphism

For `e : G ≃* G'` with `e(T) = T'`, conjugation by the induced isomorphism of linking systems
sends `Aut_typ^I(L^c_T(G))` to `Aut_typ^I(L^c_{T'}(G'))`, and `β(e α e⁻¹) = e β(α) e⁻¹`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G G' : Type u} [Group G] [Group G'] [Finite G] [Finite G'] {p : ℕ} [Fact p.Prime]

lemma isoTyp_mapFunctor (e : G ≃* G') {S : Subgroup G} {S' : Subgroup G'}
    (hS : S.map e.toMonoidHom = S') : IsoTyp p (mapFunctor p e hS) := by
  intro P
  ext m
  constructor
  · rintro ⟨_, ⟨x, hx, hxP, rfl⟩, rfl⟩
    exact ⟨e x, mem_transporter_map e hx, mem_map_of_mem _ hxP, rfl⟩
  · rintro ⟨y, hy, ⟨x, hxP, rfl⟩, rfl⟩
    exact ⟨mk p x (mem_transporter_self hxP), ⟨x, _, hxP, rfl⟩, rfl⟩

lemma mapFunctor_map_incl (e : G ≃* G') {S : Subgroup G} {S' : Subgroup G'}
    (hS : S.map e.toMonoidHom = S') {P Q : Obj p S} (h : P.val ≤ Q.val) :
    (mapFunctor p e hS).map (incl p S h) =
      incl p S' (map_mono h : ((mapFunctor p e hS).obj P).val ≤ ((mapFunctor p e hS).obj Q).val) := by
  change Mor.map p e (mk p 1 _) = mk p 1 _
  rw [Mor.map_mk]; exact mk_congr p (map_one e) _ _

variable (e : G ≃* G') {T : Sylow p G} {T' : Sylow p G'}
  (hT : (T : Subgroup G).map e.toMonoidHom = T')

/-- `e α e⁻¹` on `L^c_{T'}(G')`. -/
def conjIso (α : LAut p (T : Subgroup G)) : LAut p (T' : Subgroup G') :=
  (mapIso p e hT).symm ≪≫ α ≪≫ mapIso p e hT

lemma conjIso_fn (α : LAut p (T : Subgroup G)) :
    (conjIso e hT α).fn = mapFunctor p e.symm (map_symm_map e hT) ⋙ α.fn ⋙ mapFunctor p e hT := rfl

lemma conjIso_mem {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G)) :
    conjIso e hT α ∈ autTypI p (T' : Subgroup G') := by
  refine ⟨?_, fun P Q h => ?_⟩
  · rw [conjIso_fn]
    exact ((isoTyp_mapFunctor e.symm (map_symm_map e hT)).comp p
      ((isIsotypical_iff_isoTyp p _).1 hα.1)).comp p (isoTyp_mapFunctor e hT)
  · rw [conjIso_fn]
    obtain ⟨h₁, e₁⟩ := hα.2 ((mapFunctor p e.symm (map_symm_map e hT)).obj P)
      ((mapFunctor p e.symm (map_symm_map e hT)).obj Q) (map_mono h : ((mapFunctor p e.symm (map_symm_map e hT)).obj P).val ≤
      ((mapFunctor p e.symm (map_symm_map e hT)).obj Q).val)
    refine ⟨map_mono h₁, ?_⟩
    change (mapFunctor p e hT).map (α.fn.map ((mapFunctor p e.symm _).map (incl p _ h))) = _
    rw [mapFunctor_map_incl, e₁, mapFunctor_map_incl]

lemma conjIso_mul (α α' : LAut p (T : Subgroup G)) :
    conjIso e hT (α * α') = conjIso e hT α * conjIso e hT α' := by
  apply LAut.ext_fn
  rw [LAut.fn_mul, conjIso_fn, conjIso_fn, conjIso_fn, LAut.fn_mul]
  have h : mapFunctor p e hT ⋙ mapFunctor p e.symm (map_symm_map e hT) = 𝟭 _ := by
    rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.self_trans_symm e) _ (map_refl _),
      mapFunctor_refl]
  calc mapFunctor p e.symm (map_symm_map e hT) ⋙ (α'.fn ⋙ α.fn) ⋙ mapFunctor p e hT =
      mapFunctor p e.symm (map_symm_map e hT) ⋙ α'.fn ⋙ 𝟭 _ ⋙ α.fn ⋙ mapFunctor p e hT := rfl
    _ = _ := by rw [← h]; rfl

/-- `β(e α e⁻¹)(e x) = e(β(α)(x))`. -/
lemma betaFun_conjIso {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
    (x : (T : Subgroup G)) (hx : e x ∈ (T' : Subgroup G')) :
    ((betaFun (conjIso_mem e hT hα) ⟨e x, hx⟩ : _) : G') = e (betaFun hα x) := by
  have hβ := (betaFun (conjIso_mem e hT hα) ⟨e x, hx⟩).2
  have e1 := map_mk_top (conjIso_mem e hT hα) ⟨e x, hx⟩
  -- the same morphism computed through `α`
  have hobj : (mapFunctor p e.symm (map_symm_map e hT)).obj (topObj T') = topObj T :=
    Obj.ext (map_symm_map e hT)
  have h1 : HEq ((mapFunctor p e.symm (map_symm_map e hT)).map
      (show topObj T' ⟶ topObj T' from mk p (e x) (mem_transporter_self hx)))
      (show topObj T ⟶ topObj T from mk p (x : G) (mem_transporter_self x.2)) := by
    rw [mapFunctor_map_mk]
    exact mk_heq p (congrArg Obj.val hobj) (congrArg Obj.val hobj) (by simp) _ _
  have h2 := Functor.map_heq' α.fn hobj hobj h1
  rw [map_mk_top hα x] at h2
  have h3 := Functor.map_heq' (mapFunctor p e hT) (congrArg α.fn.obj hobj) (congrArg α.fn.obj hobj) h2
  rw [mapFunctor_map_mk] at h3
  change HEq ((conjIso e hT α).fn.map (show topObj T' ⟶ topObj T' from
    mk p (e x) (mem_transporter_self hx))) _ at h3
  rw [e1] at h3
  erw [mapFunctor_map_mk] at h3
  have hc := mk_rel_of_heq (congrArg Obj.val (congrArg (mapFunctor p e hT).obj
    (congrArg α.fn.obj hobj))) (congrArg Obj.val (congrArg (mapFunctor p e hT).obj
    (congrArg α.fn.obj hobj))) h3
  have hval : ((conjIso e hT α).fn.obj (topObj T')).val = T' := val_obj_top (conjIso_mem e hT hα)
  have hR := ((conjIso e hT α).fn.obj (topObj T')).2
  have hmem : e (betaFun hα x : G) ∈ (T' : Subgroup G') := by
    rw [← hT]; exact mem_map_of_mem _ (betaFun hα x).2
  have := eq_one_of_mem_opCent T' hR hc (mul_mem (inv_mem hβ) hmem)
  rw [← mul_inv_cancel_left (betaFun (conjIso_mem e hT hα) ⟨e x, hx⟩ : G') (e (betaFun hα x : G)),
    this, mul_one]

end AndersenOliverVentura.Tame
