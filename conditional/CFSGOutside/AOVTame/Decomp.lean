import CFSGOutside.AOVTame.Swap

/-!
# AOV tameness: a factor-preserving `α ∈ Aut_typ^I(L(A × B))` is `Φ(α_A, Id) ∘ Φ(Id, α_B)`

This is the injectivity of `Ψ` in AOV, proof of Theorem 3.6, in the case at hand.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

section General
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}

lemma eq_mk_of_heq {X Y X' Y' : Obj p S} (hX : X = X') (hY : Y = Y') {m : X ⟶ Y} {g : G}
    {hg : g ∈ transporter X'.val Y'.val} (h : HEq m (show X' ⟶ Y' from mk p g hg)) :
    ∃ hg' : g ∈ transporter X.val Y.val, m = mk p g hg' := by
  subst hX hY; exact ⟨hg, eq_of_heq h⟩

/-- A morphism is determined by any extension to larger objects. -/
lemma eq_mk_of_comp_incl {X Y X' Y' : Obj p S} (hX : X.val ≤ X'.val) (hY : Y.val ≤ Y'.val)
    (m : X ⟶ Y) {g : G} (hg' : g ∈ transporter X'.val Y'.val)
    (e : m ≫ incl p S hY = incl p S hX ≫ (show X' ⟶ Y' from mk p g hg')) :
    ∃ hg : g ∈ transporter X.val Y.val, m = mk p g hg := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := Quotient.exists_rep m
  have e' : (mk p (1 * h) (mul_mem_transporter (one_mem_transporter hY) hh) : Mor p X.val Y'.val) =
      mk p (g * 1) (mul_mem_transporter hg' (one_mem_transporter hX)) := e
  have hc : h⁻¹ * g ∈ opCent p X.val := by simpa using (mk_eq_mk p).1 e'
  have hcC := opCent_le_centralizer p _ hc
  have hgT : g ∈ transporter X.val Y.val := by
    intro x hx
    have h1 := hh x hx
    have h2 : (h⁻¹ * g) * x = x * (h⁻¹ * g) := (mem_centralizer_iff.1 hcC x hx).symm
    have : g * x * g⁻¹ = h * x * h⁻¹ := by
      calc g * x * g⁻¹ = h * ((h⁻¹ * g) * x) * (h⁻¹ * g)⁻¹ * h⁻¹ := by group
        _ = h * (x * (h⁻¹ * g)) * (h⁻¹ * g)⁻¹ * h⁻¹ := by rw [h2]
        _ = h * x * h⁻¹ := by group
    rw [this]; exact h1
  exact ⟨hgT, (mk_eq_mk p).2 hc⟩

variable {T : Sylow p G} {α : LAut p (T : Subgroup G)} (hα : α ∈ autTypI p (T : Subgroup G))
include hα

/-- `α` of a restriction is the restriction of `α`. -/
lemma alpha_restrict {X Y X' Y' : Obj p (T : Subgroup G)} (hX : X.val ≤ X'.val) (hY : Y.val ≤ Y'.val)
    {g : G} (hg : g ∈ transporter X.val Y.val) (hg' : g ∈ transporter X'.val Y'.val) {k : G}
    {hk' : k ∈ transporter (α.fn.obj X').val (α.fn.obj Y').val}
    (e : α.fn.map (show X' ⟶ Y' from mk p g hg') = mk p k hk') :
    ∃ hk : k ∈ transporter (α.fn.obj X).val (α.fn.obj Y).val,
      α.fn.map (show X ⟶ Y from mk p g hg) = mk p k hk := by
  have e0 : (show X ⟶ Y from mk p g hg) ≫ incl p _ hY = incl p _ hX ≫ (show X' ⟶ Y' from mk p g hg') :=
    mk_congr p (by simp) _ _
  have e1 := congrArg α.fn.map e0
  rw [α.fn.map_comp, α.fn.map_comp, e] at e1
  obtain ⟨hY', eY⟩ := hα.2 Y Y' hY
  obtain ⟨hX', eX⟩ := hα.2 X X' hX
  rw [eY, eX] at e1
  exact eq_mk_of_comp_incl hX' hY' _ hk' e1

end General

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

/-- `Φ(Id, γ)` for `γ ∈ Aut_typ^I(L(B))`. -/
noncomputable def phiBAut {γ : LAut p (SB : Subgroup B)} (hγ : γ ∈ autTypI p (SB : Subgroup B)) :
    LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  conjIso (MulEquiv.prodComm : B × A ≃* A × B) (map_prodComm_prodSylow SB SA) (phiAut SA hγ)

lemma phiBAut_mem {γ : LAut p (SB : Subgroup B)} (hγ : γ ∈ autTypI p (SB : Subgroup B)) :
    phiBAut (SA := SA) hγ ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  conjIso_mem _ _ (phiAut_mem hγ)

/-- The second projection of an object of `L(A × B)`. -/
def proj₂ (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) : Obj p (SB : Subgroup B) :=
  ⟨P.val.map (MonoidHom.snd A B), isCentric_snd P.2⟩

section Alpha
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)

variable (SA) in
/-- `S_A × P` as an object of `L(A × B)`, in the form produced by the swap. -/
noncomputable def objB (P : Obj p (SB : Subgroup B)) :
    Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  (mapFunctor p (MulEquiv.prodComm : A × B ≃* B × A).symm
    (map_symm_map _ (map_prodComm_prodSylow SA SB))).obj (prodObj SA P)

lemma objB_val (P : Obj p (SB : Subgroup B)) :
    (objB SA P).val = (SA : Subgroup A).prod P.val := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨y, x⟩, ⟨hy, hx⟩, e⟩
    change (x, y) = (a, b) at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨hx, hy⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(b, a), ⟨hb, ha⟩, rfl⟩

lemma mem_transporter_objB {P Q : Obj p (SB : Subgroup B)} {g : B} (hg : g ∈ transporter P.val Q.val) :
    ((1, g) : A × B) ∈ transporter (objB SA P).val (objB SA Q).val := by
  rw [objB_val, objB_val]
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨by simpa using hx, hg y hy⟩

include hf in
/-- Purity for the second factor: `α([(1, g)]) = [(1, α_B[g])]`. -/
lemma pureB {P Q : Obj p (SB : Subgroup B)} {g : B} (hg : g ∈ transporter P.val Q.val) :
    ∃ (k : B) (hk : k ∈ transporter ((lautB SA hα hf).fn.obj P).val ((lautB SA hα hf).fn.obj Q).val)
      (hk' : ((1, k) : A × B) ∈ transporter (α.fn.obj (objB SA P)).val (α.fn.obj (objB SA Q)).val),
      (lautB SA hα hf).fn.map (show P ⟶ Q from mk p g hg) = mk p k hk ∧
      α.fn.map (show objB SA P ⟶ objB SA Q from mk p (1, g) (mem_transporter_objB hg)) = mk p (1, k) hk' := by
  obtain ⟨k, hk1, e1⟩ := pure_liftA (swapAut_mem hα) (presFactors_swap hα hf) P Q hg
  set eAB : A × B ≃* B × A := MulEquiv.prodComm
  have hT := map_prodComm_prodSylow SA SB
  have hcomp : mapFunctor p eAB hT ⋙ mapFunctor p eAB.symm (map_symm_map eAB hT) = 𝟭 _ := by
    rw [mapFunctor_comp, mapFunctor_congr p (MulEquiv.self_trans_symm eAB) _ (map_refl _),
      mapFunctor_refl]
  set Z := α.fn.map (show objB SA P ⟶ objB SA Q from mk p (1, g) (mem_transporter_objB hg))
  have e2 : (mapFunctor p eAB hT).map Z = mk p (k, 1) hk1 := e1
  have h3 := Functor.hcongr_hom hcomp Z
  change HEq ((mapFunctor p eAB.symm (map_symm_map eAB hT)).map ((mapFunctor p eAB hT).map Z)) Z at h3
  rw [e2] at h3
  change HEq (Mor.map p eAB.symm (mk p (k, 1) hk1)) Z at h3
  rw [Mor.map_mk] at h3
  obtain ⟨hk', e3⟩ := eq_mk_of_heq (Functor.congr_obj hcomp _).symm (Functor.congr_obj hcomp _).symm h3.symm
  refine ⟨k, ?_, hk', ?_, e3⟩
  · have := mem_transporter_fst hk1
    exact this
  · change projFst ((swapAut α).fn.map (liftA SA (show P ⟶ Q from mk p g hg))) = _
    rw [e1]; rfl

end Alpha

section Main
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

lemma mem_alpha_obj (R : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) {y : A × B} :
    y ∈ (α.fn.obj R).val ↔ ∃ x ∈ R.val, ∃ (h1 : x.1 ∈ (SA : Subgroup A)) (h2 : x.2 ∈ (SB : Subgroup B)),
      y = (bA hα x.1 h1, bB hα x.2 h2) := by
  rw [obj_val_eq hα]
  constructor
  · intro hy
    obtain ⟨hyS, hz⟩ := (mem_bmap_iff (beta hα)).1 hy
    set z := (beta hα).symm ⟨y, hyS⟩ with hz_def
    have hyz : y = (((beta hα) z : _) : A × B) := by rw [hz_def, MulEquiv.apply_symm_apply]
    refine ⟨z, hz, z.2.1, z.2.2, ?_⟩
    rw [hyz, beta_apply]
    exact betaFun_pair hα hf _ _ _ _
  · rintro ⟨x, hx, h1, h2, rfl⟩
    have := mem_bmap (β := beta hα) (⟨x, R.2.1 hx⟩ : _) hx
    rw [beta_apply] at this
    have e : ((betaFun hα ⟨x, R.2.1 hx⟩ : _) : A × B) = (bA hα x.1 h1, bB hα x.2 h2) :=
      betaFun_pair hα hf _ _ _ _
    rwa [e] at this

lemma mem_phiB_obj (R : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) {y : A × B} :
    y ∈ ((phiBAut (SA := SA) (lautB_mem hα hf)).fn.obj R).val ↔
      ∃ x ∈ R.val, ∃ h2 : x.2 ∈ (SB : Subgroup B), y = (x.1, bB hα x.2 h2) := by
  change y ∈ (bmap (bX SA (lautB_mem hα hf)) (R.val.map
    (MulEquiv.prodComm : B × A ≃* A × B).symm.toMonoidHom)).map
      (MulEquiv.prodComm : B × A ≃* A × B).toMonoidHom ↔ _
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x', ⟨x, hx, rfl⟩, h1, h2, rfl⟩ := (mem_bmap_bX_iff (lautB_mem hα hf)).1 hv
    refine ⟨x, hx, h1, ?_⟩
    change (x.1, ((betaFun (lautB_mem hα hf) ⟨x.2, h1⟩ : _) : B)) = _
    rw [betaFun_lautB]
  · rintro ⟨x, hx, h2, rfl⟩
    refine ⟨(bB hα x.2 h2, x.1), (mem_bmap_bX_iff (lautB_mem hα hf)).2
      ⟨(x.2, x.1), ⟨x, hx, rfl⟩, h2, (R.2.1 hx).1, ?_⟩, rfl⟩
    change _ = (((betaFun (lautB_mem hα hf) ⟨x.2, h2⟩ : _) : B), x.1)
    rw [betaFun_lautB]

lemma phiB_fst (R : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    proj₁ ((phiBAut (SA := SA) (lautB_mem hα hf)).fn.obj R) = proj₁ R := by
  apply Obj.ext
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, h2, rfl⟩ := (mem_phiB_obj hα hf R).1 hy
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (mem_phiB_obj hα hf R).2 ⟨x, hx, (R.2.1 hx).2, rfl⟩, rfl⟩

lemma decomp_obj (R : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    α.fn.obj R = ((phiBAut (SA := SA) (lautB_mem hα hf)).fn ⋙
      phiFunctor SB (lautA_mem hα hf)).obj R := by
  apply Obj.ext
  change (α.fn.obj R).val = bmap (bX SB (lautA_mem hα hf))
    ((phiBAut (SA := SA) (lautB_mem hα hf)).fn.obj R).val
  ext y
  rw [mem_alpha_obj hα hf, mem_bmap_bX_iff]
  constructor
  · rintro ⟨x, hx, h1, h2, rfl⟩
    refine ⟨(x.1, bB hα x.2 h2), (mem_phiB_obj hα hf R).2 ⟨x, hx, h2, rfl⟩, h1, bB_mem hα _ h2, ?_⟩
    rw [betaFun_lautA]
  · rintro ⟨w, hw, h1, h2, rfl⟩
    obtain ⟨x, hx, hx2, rfl⟩ := (mem_phiB_obj hα hf R).1 hw
    refine ⟨x, hx, h1, hx2, ?_⟩
    change (((betaFun (lautA_mem hα hf) ⟨x.1, h1⟩ : _) : A), _) = _
    rw [betaFun_lautA]

end Main

lemma bA_congr {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) {a a' : A}
    (h : a = a') (ha : a ∈ (SA : Subgroup A)) (ha' : a' ∈ (SA : Subgroup A)) :
    bA hα a ha = bA hα a' ha' := by subst h; rfl

lemma bB_congr {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) {b b' : B}
    (h : b = b') (hb : b ∈ (SB : Subgroup B)) (hb' : b' ∈ (SB : Subgroup B)) :
    bB hα b hb = bB hα b' hb' := by subst h; rfl

section Thm
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

/-- `α([g]) = [(h₁, k₂)]` where `α_A[g₁] = [h₁]` and `α_B[g₂] = [k₂]`. -/
lemma alpha_map_mk {R R' : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))} {g : A × B}
    (hg : g ∈ transporter R.val R'.val) {h₁ : A}
    {hh₁ : h₁ ∈ transporter ((lautA SB hα hf).fn.obj (proj₁ R)).val ((lautA SB hα hf).fn.obj (proj₁ R')).val}
    (e₁ : (lautA SB hα hf).fn.map (show proj₁ R ⟶ proj₁ R' from mk p g.1 (mem_transporter_fst hg)) =
      mk p h₁ hh₁) {k₂ : B}
    {hk₂ : k₂ ∈ transporter ((lautB SA hα hf).fn.obj (proj₂ R)).val ((lautB SA hα hf).fn.obj (proj₂ R')).val}
    (e₂ : (lautB SA hα hf).fn.map (show proj₂ R ⟶ proj₂ R' from mk p g.2 (mem_transporter_snd hg)) =
      mk p k₂ hk₂) :
    ∃ h : ((h₁, k₂) : A × B) ∈ transporter (α.fn.obj R).val (α.fn.obj R').val,
      α.fn.map (show R ⟶ R' from mk p g hg) = mk p (h₁, k₂) h := by
  set R₁ := proj₁ R
  set R₁' := proj₁ R'
  set R₂ := proj₂ R
  set R₂' := proj₂ R'
  have hg₁ : g.1 ∈ transporter R₁.val R₁'.val := mem_transporter_fst hg
  have hg₂ : g.2 ∈ transporter R₂.val R₂'.val := mem_transporter_snd hg
  -- the first factor
  obtain ⟨a, ha, eA⟩ := pure_liftA hα hf R₁ R₁' hg₁
  have eA' : (lautA SB hα hf).fn.map (show R₁ ⟶ R₁' from mk p g.1 hg₁) =
      mk p a (mem_transporter_fst ha) := by
    change projFst (α.fn.map (liftA SB (show R₁ ⟶ R₁' from mk p g.1 hg₁))) = _
    rw [eA]; rfl
  have haa : h₁⁻¹ * a ∈ opCent p ((lautA SB hα hf).fn.obj R₁).val :=
    (mk_eq_mk p).1 (e₁.symm.trans eA')
  -- the second factor
  obtain ⟨b, hb, hb', eBl, eBa⟩ := pureB hα hf hg₂
  have hbb : k₂⁻¹ * b ∈ opCent p ((lautB SA hα hf).fn.obj R₂).val :=
    (mk_eq_mk p).1 (e₂.symm.trans eBl)
  -- products
  let Rh : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
    ⟨R₁.val.prod R₂.val, isCentric_prod R₁.2 R₂.2⟩
  let M : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
    ⟨R₁'.val.prod R₂.val, isCentric_prod R₁'.2 R₂.2⟩
  let Rh' : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
    ⟨R₁'.val.prod R₂'.val, isCentric_prod R₁'.2 R₂'.2⟩
  have t1 : ((g.1, 1) : A × B) ∈ transporter Rh.val M.val := mem_transporter_prod hg₁
  have t2 : ((1, g.2) : A × B) ∈ transporter M.val Rh'.val := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨by simpa using hx, hg₂ y hy⟩
  obtain ⟨u1, e1⟩ := alpha_restrict hα (X := Rh) (Y := M) (X' := prodObj SB R₁) (Y' := prodObj SB R₁')
    (prod_mono le_rfl R₂.2.1) (prod_mono le_rfl R₂.2.1) t1 (mem_transporter_prod hg₁) eA
  obtain ⟨u2, e2⟩ := alpha_restrict hα (X := M) (Y := Rh') (X' := objB SA R₂) (Y' := objB SA R₂')
    (by rw [objB_val]; exact prod_mono R₁'.2.1 le_rfl) (by rw [objB_val]; exact prod_mono R₁'.2.1 le_rfl)
    t2 (mem_transporter_objB hg₂) eBa
  have t3 : g ∈ transporter Rh.val Rh'.val := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hg₁ x hx, hg₂ y hy⟩
  have e3 : α.fn.map (show Rh ⟶ Rh' from mk p g t3) = mk p (a, b) (by
      have := mul_mem_transporter u2 u1
      simpa using this) := by
    have : (show Rh ⟶ Rh' from mk p g t3) =
        (show Rh ⟶ M from mk p (g.1, 1) t1) ≫ (show M ⟶ Rh' from mk p (1, g.2) t2) :=
      mk_congr p (by ext <;> simp) _ _
    rw [this, α.fn.map_comp, e1, e2]
    exact mk_congr p (by ext <;> simp) _ _
  have hRRh : R.val ≤ Rh.val := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hRRh' : R'.val ≤ Rh'.val := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  obtain ⟨u3, e4⟩ := alpha_restrict hα hRRh hRRh' hg t3 e3
  -- change representatives
  have hc : ((h₁, k₂) : A × B)⁻¹ * (a, b) ∈ opCent p (α.fn.obj R).val := by
    have hfst : (α.fn.obj R).val.map (MonoidHom.fst A B) = ((lautA SB hα hf).fn.obj R₁).val := by
      change _ = (α.fn.obj (prodObj SB R₁)).val.map (MonoidHom.fst A B)
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, hx, h1, h2, rfl⟩ := (mem_alpha_obj hα hf R).1 hw
        exact ⟨(bA hα x.1 h1, bB hα 1 (one_mem _)), (mem_alpha_obj hα hf (prodObj SB R₁)).2
          ⟨(x.1, 1), ⟨⟨x, hx, rfl⟩, one_mem _⟩, h1, one_mem _, rfl⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, ⟨⟨x', hx', hx1⟩, -⟩, h1, h2, rfl⟩ := (mem_alpha_obj hα hf (prodObj SB R₁)).1 hw
        refine ⟨(bA hα x'.1 (R.2.1 hx').1, bB hα x'.2 (R.2.1 hx').2), (mem_alpha_obj hα hf R).2
          ⟨x', hx', (R.2.1 hx').1, (R.2.1 hx').2, rfl⟩, ?_⟩
        exact bA_congr hα hx1 (R.2.1 hx').1 h1
    have hsnd : (α.fn.obj R).val.map (MonoidHom.snd A B) = ((lautB SA hα hf).fn.obj R₂).val := by
      ext y
      rw [show ((lautB SA hα hf).fn.obj R₂).val =
        ((swapAut α).fn.obj (prodObj SA R₂)).val.map (MonoidHom.fst B A) from rfl]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, hx, h1, h2, rfl⟩ := (mem_alpha_obj hα hf R).1 hw
        refine ⟨(bA (swapAut_mem hα) x.2 h2, bB (swapAut_mem hα) 1 (one_mem _)),
          (mem_alpha_obj (swapAut_mem hα) (presFactors_swap hα hf) (prodObj SA R₂)).2
            ⟨(x.2, 1), ⟨⟨x, hx, rfl⟩, one_mem _⟩, h2, one_mem _, rfl⟩, ?_⟩
        change bA (swapAut_mem hα) x.2 h2 = bB hα x.2 h2
        exact bA_swap hα hf h2
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨x, ⟨⟨x', hx', hx1⟩, -⟩, h1, h2, rfl⟩ :=
          (mem_alpha_obj (swapAut_mem hα) (presFactors_swap hα hf) (prodObj SA R₂)).1 hw
        refine ⟨(bA hα x'.1 (R.2.1 hx').1, bB hα x'.2 (R.2.1 hx').2), (mem_alpha_obj hα hf R).2
          ⟨x', hx', (R.2.1 hx').1, (R.2.1 hx').2, rfl⟩, ?_⟩
        change bB hα x'.2 (R.2.1 hx').2 = bA (swapAut_mem hα) x.1 h1
        rw [bA_swap hα hf]
        exact bB_congr hα hx1 (R.2.1 hx').2 h1
    have := opCent_pair (P := (α.fn.obj R).val) (a := h₁⁻¹ * a) (b := k₂⁻¹ * b)
      (by rw [hfst]; exact haa) (by rw [hsnd]; exact hbb)
    simpa using this
  refine ⟨?_, e4.trans ((mk_eq_mk p).2 ?_)⟩
  · intro x hx
    have hcC := opCent_le_centralizer p _ hc
    have h5 := u3 x hx
    have h6 : (((h₁, k₂) : A × B)⁻¹ * (a, b)) * x = x * (((h₁, k₂) : A × B)⁻¹ * (a, b)) :=
      (mem_centralizer_iff.1 hcC x hx).symm
    have : ((h₁, k₂) : A × B) * x * ((h₁, k₂) : A × B)⁻¹ = (a, b) * x * (a, b)⁻¹ := by
      calc ((h₁, k₂) : A × B) * x * ((h₁, k₂) : A × B)⁻¹ =
          (a, b) * ((((h₁, k₂) : A × B)⁻¹ * (a, b))⁻¹ * x * (((h₁, k₂) : A × B)⁻¹ * (a, b))) *
            (a, b)⁻¹ := by group
        _ = (a, b) * ((((h₁, k₂) : A × B)⁻¹ * (a, b))⁻¹ * (x * (((h₁, k₂) : A × B)⁻¹ * (a, b)))) *
            (a, b)⁻¹ := by group
        _ = _ := by rw [← h6]; group
    rw [this]; exact h5
  · have := inv_mem hc
    simpa [mul_assoc] using this

end Thm

section Decomp
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

/-- **Decomposition** (injectivity of `Ψ`, AOV proof of Theorem 3.6): a factor-preserving
`α ∈ Aut_typ^I(L(A × B))` is `Φ(α_A, Id) ∘ Φ(Id, α_B)`. -/
theorem decomp : α.fn = (phiBAut (SA := SA) (lautB_mem hα hf)).fn ⋙ phiFunctor SB (lautA_mem hα hf) := by
  set eBA : B × A ≃* A × B := MulEquiv.prodComm
  have hT := map_prodComm_prodSylow SB SA
  refine Functor.hext (decomp_obj hα hf) ?_
  rintro R R' ⟨⟨g, hg⟩⟩
  have hg₁ : g.1 ∈ transporter (proj₁ R).val (proj₁ R').val := mem_transporter_fst hg
  have hg₂ : g.2 ∈ transporter (proj₂ R).val (proj₂ R').val := mem_transporter_snd hg
  obtain ⟨⟨h₁, hh₁⟩, e₁⟩ := Quotient.exists_rep
    ((lautA SB hα hf).fn.map (show proj₁ R ⟶ proj₁ R' from mk p g.1 hg₁))
  obtain ⟨⟨k₂, hk₂⟩, e₂⟩ := Quotient.exists_rep
    ((lautB SA hα hf).fn.map (show proj₂ R ⟶ proj₂ R' from mk p g.2 hg₂))
  obtain ⟨hm, eL⟩ := alpha_map_mk hα hf hg e₁.symm e₂.symm
  change HEq (α.fn.map (show R ⟶ R' from mk p g hg))
    (phiMor SB (lautA_mem hα hf) ((phiBAut (SA := SA) (lautB_mem hα hf)).fn.map
      (show R ⟶ R' from mk p g hg)))
  rw [eL]
  -- the morphism `Φ(Id, α_B)([g]) = [(g₁, k₂)]`
  set X := (mapFunctor p eBA.symm (map_symm_map eBA hT)).obj R
  set X' := (mapFunctor p eBA.symm (map_symm_map eBA hT)).obj R'
  have hX : proj₂ R = proj₁ X := Obj.ext (by
    change R.val.map (MonoidHom.snd A B) = (R.val.map eBA.symm.toMonoidHom).map (MonoidHom.fst B A)
    rw [map_map]; rfl)
  have hX' : proj₂ R' = proj₁ X' := Obj.ext (by
    change R'.val.map (MonoidHom.snd A B) = (R'.val.map eBA.symm.toMonoidHom).map (MonoidHom.fst B A)
    rw [map_map]; rfl)
  have hgX : eBA.symm g ∈ transporter X.val X'.val := mem_transporter_map eBA.symm hg
  have hgX1 : (eBA.symm g).1 ∈ transporter (proj₁ X).val (proj₁ X').val := mem_transporter_fst hgX
  have h2 := Functor.map_heq' (lautB SA hα hf).fn hX hX'
    (mk_heq p (congrArg Obj.val hX) (congrArg Obj.val hX') rfl hg₂
      hgX1)
  rw [← e₂] at h2
  obtain ⟨hk₂', eB⟩ := eq_mk_of_heq (congrArg (lautB SA hα hf).fn.obj hX).symm
    (congrArg (lautB SA hα hf).fn.obj hX').symm h2.symm
  have eB' := phiMor_mk (lautB_mem hα hf) hgX hk₂' eB
  have ePhiB : (phiBAut (SA := SA) (lautB_mem hα hf)).fn.map (show R ⟶ R' from mk p g hg) =
      mk p (g.1, k₂) (by
        have := mem_transporter_map eBA (phi_transporter (lautB_mem hα hf) hgX hk₂' eB)
        exact this) := by
    change (mapFunctor p eBA hT).map (phiMor SA (lautB_mem hα hf)
      (show X ⟶ X' from mk p (eBA.symm g) hgX)) = _
    rw [eB', mapFunctor_map_mk]
    rfl
  rw [ePhiB]
  -- the morphism `Φ(α_A, Id)([(g₁, k₂)]) = [(h₁, k₂)]`
  set Y := (phiBAut (SA := SA) (lautB_mem hα hf)).fn.obj R
  set Y' := (phiBAut (SA := SA) (lautB_mem hα hf)).fn.obj R'
  have hY := phiB_fst hα hf R
  have hY' := phiB_fst hα hf R'
  have hgY : ((g.1, k₂) : A × B) ∈ transporter Y.val Y'.val := by
    have := mem_transporter_map eBA (phi_transporter (lautB_mem hα hf) hgX hk₂' eB)
    exact this
  have hgY1 : ((g.1, k₂) : A × B).1 ∈ transporter (proj₁ Y).val (proj₁ Y').val :=
    mem_transporter_fst hgY
  have h3 := Functor.map_heq' (lautA SB hα hf).fn hY.symm hY'.symm
    (mk_heq p (congrArg Obj.val hY.symm) (congrArg Obj.val hY'.symm) rfl hg₁
      hgY1)
  rw [← e₁] at h3
  obtain ⟨hh₁', eA⟩ := eq_mk_of_heq (congrArg (lautA SB hα hf).fn.obj hY)
    (congrArg (lautA SB hα hf).fn.obj hY') h3.symm
  rw [phiMor_mk (lautA_mem hα hf) hgY hh₁' eA]
  exact mk_heq p (congrArg Obj.val (decomp_obj hα hf R)) (congrArg Obj.val (decomp_obj hα hf R'))
    rfl _ _

end Decomp

end AndersenOliverVentura.Tame
