import CFSGOutside.AOVTame.PsiMain

/-!
# AOV tameness: the first component `α_A ∈ Aut_typ^I(L(A))` of a factor-preserving `α`

For `α ∈ Aut_typ^I(L(A × B))` preserving both factors, `α_A` sends `P` to the first projection of
`α(P × S_B)` and `[g]` to the first coordinate of `α([(g, 1)])`. By purity (claim (3.6b)),
`α([(g, 1)]) = [(α_A[g], 1)]`, and `α ↦ α_A` is multiplicative, so `α_A` is an automorphism.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

/-- `[(h₁, h₂)] ↦ [h₁]`. -/
def projFst {R R' : Subgroup (A × B)} :
    Mor p R R' → Mor p (R.map (MonoidHom.fst A B)) (R'.map (MonoidHom.fst A B)) :=
  Quotient.lift (fun g : transporter R R' => Tame.mk p (g : A × B).1 (mem_transporter_fst g.2))
    (by
      rintro ⟨g, hg⟩ ⟨g', hg'⟩ (e : g⁻¹ * g' ∈ opCent p R)
      apply (mk_eq_mk p).2
      have := opCent_fst e
      simpa using this)

lemma projFst_comp {R R' R'' : Subgroup (A × B)} (f : Mor p R R') (g : Mor p R' R'') :
    projFst (comp p g f) = comp p (projFst g) (projFst f) := by
  obtain ⟨⟨a, ha⟩⟩ := f
  obtain ⟨⟨b, hb⟩⟩ := g
  rfl

lemma mem_prodSylow_fst {x : A × B} (hx : x ∈ ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    x.1 ∈ (SA : Subgroup A) := hx.1

lemma mem_prodSylow_snd {x : A × B} (hx : x ∈ ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    x.2 ∈ (SB : Subgroup B) := hx.2

section
variable {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
  (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf' : PresFactors hα')

include hf hf' in
lemma presFactors_mul : PresFactors (mul_mem hα hα') := by
  constructor
  · intro a ha
    rw [betaFun_mul_aut hα hα']
    have e : ((betaFun hα' ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ : _) : A × B) =
        (bA hα' a ha, 1) := by
      have := betaFun_pair hα' hf' a ha 1 (one_mem _)
      rw [this]
      congr 1
      have h1 : betaFun hα' ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ = 1 := by
        rw [show (⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ :
          ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) = 1 from rfl, ← beta_apply]
        exact map_one _
      show ((betaFun hα' ⟨((1 : A), (1 : B)), _⟩ : _) : A × B).2 = 1
      rw [h1]; rfl
    have e' : betaFun hα' ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ =
        ⟨(bA hα' a ha, 1), mem_prodSylow (bA_mem hα' a ha) (one_mem _)⟩ := Subtype.ext e
    rw [e']
    exact hf.fst (bA hα' a ha) (bA_mem hα' a ha)
  · intro b hb
    rw [betaFun_mul_aut hα hα']
    have e : ((betaFun hα' ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ : _) : A × B) =
        (1, bB hα' b hb) := by
      have := betaFun_pair hα' hf' 1 (one_mem _) b hb
      rw [this, bA_one hα' hf']
    have e' : betaFun hα' ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ =
        ⟨(1, bB hα' b hb), mem_prodSylow (one_mem _) (bB_mem hα' b hb)⟩ := Subtype.ext e
    rw [e']
    exact hf.snd (bB hα' b hb) (bB_mem hα' b hb)

include hf in
lemma bB_one : bB hα (1 : B) (one_mem _) = 1 := by
  have h0 : betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ = 1 := by
    rw [show (⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ :
      ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) = 1 from rfl, ← beta_apply]
    exact map_one _
  show ((betaFun hα ⟨((1 : A), (1 : B)), mem_prodSylow (one_mem _) (one_mem _)⟩ : _) : A × B).2 = 1
  rw [h0]; rfl

include hf in
lemma bA_injective {a a' : A} (ha : a ∈ (SA : Subgroup A)) (ha' : a' ∈ (SA : Subgroup A))
    (e : bA hα a ha = bA hα a' ha') : a = a' := by
  have h1 := betaFun_pair hα hf a ha 1 (one_mem _)
  have h2 := betaFun_pair hα hf a' ha' 1 (one_mem _)
  have : betaFun hα ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ =
      betaFun hα ⟨(a', 1), mem_prodSylow ha' (one_mem _)⟩ := Subtype.ext (by rw [h1, h2, e])
  have h3 := congrArg Subtype.val (betaFun_injective hα this)
  simpa using congrArg Prod.fst h3

include hf in
lemma presFactors_inv : PresFactors (inv_mem hα) := by
  constructor
  · intro a ha
    set z := betaFun (inv_mem hα) ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ with hz
    have h1 : betaFun hα z = ⟨(a, 1), mem_prodSylow ha (one_mem _)⟩ := betaFun_inv_aut' hα _
    have h2 : ((betaFun hα z : _) : A × B) =
        (bA hα (z : A × B).1 (mem_prodSylow_fst z.2), bB hα (z : A × B).2 (mem_prodSylow_snd z.2)) :=
      betaFun_pair hα hf _ _ _ _
    have h3 := congrArg Prod.snd (h2.symm.trans (congrArg Subtype.val h1))
    simp only at h3
    rw [← bB_one hα hf] at h3
    exact bB_injective hα hf _ _ h3
  · intro b hb
    set z := betaFun (inv_mem hα) ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ with hz
    have h1 : betaFun hα z = ⟨(1, b), mem_prodSylow (one_mem _) hb⟩ := betaFun_inv_aut' hα _
    have h2 : ((betaFun hα z : _) : A × B) =
        (bA hα (z : A × B).1 (mem_prodSylow_fst z.2), bB hα (z : A × B).2 (mem_prodSylow_snd z.2)) :=
      betaFun_pair hα hf _ _ _ _
    have h3 := congrArg Prod.fst (h2.symm.trans (congrArg Subtype.val h1))
    simp only at h3
    rw [← bA_one hα hf] at h3
    exact bA_injective hα hf _ _ h3

end

section Fn
variable {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))

variable (SB) in
/-- `α_A` as a functor `L(A) → L(A)`. -/
noncomputable def fnA : Obj p (SA : Subgroup A) ⥤ Obj p (SA : Subgroup A) where
  obj := objA (α := α)
  map ψ := projFst (α.fn.map (liftA SB ψ))
  map_id P := by
    change projFst (α.fn.map (liftA SB (𝟙 P))) = _
    rw [liftA_id, α.fn.map_id]; rfl
  map_comp f g := by
    change projFst (α.fn.map (liftA SB (f ≫ g))) = _
    rw [liftA_comp, α.fn.map_comp]
    exact projFst_comp _ _

variable (hf : PresFactors hα)
include hf

/-- `α([(g,1)]) = [(α_A[g], 1)]`. -/
lemma liftA_fnA {P Q : Obj p (SA : Subgroup A)} (ψ : P ⟶ Q) :
    HEq (α.fn.map (liftA SB ψ)) (liftA SB ((fnA SB (α := α)).map ψ)) := by
  obtain ⟨⟨g, hg⟩⟩ := ψ
  obtain ⟨h, hh, e⟩ := pure_liftA hα hf P Q hg
  change HEq (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg)))
    (liftA SB (show objA (α := α) P ⟶ objA (α := α) Q from
      projFst (α.fn.map (liftA SB (show P ⟶ Q from Tame.mk p g hg)))))
  rw [e]
  exact mk_heq p (congrArg Obj.val (obj_prodObj hα hf P)) (congrArg Obj.val (obj_prodObj hα hf Q))
    rfl _ _

end Fn

lemma projFst_heq {R₁ R₂ R₁' R₂' : Subgroup (A × B)} (h₁ : R₁ = R₂) (h₂ : R₁' = R₂')
    {m : Mor p R₁ R₁'} {m' : Mor p R₂ R₂'} (h : HEq m m') : HEq (projFst m) (projFst m') := by
  subst h₁ h₂; cases h; rfl

lemma fnA_congr {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (h : α = α') : fnA SB (α := α) = fnA SB (α := α') := by subst h; rfl

lemma fnA_one : fnA SB (α := (1 : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))) =
    𝟭 (Obj p (SA : Subgroup A)) := by
  have hobj : ∀ P : Obj p (SA : Subgroup A), (fnA SB (α := 1)).obj P = P := fun P =>
    Obj.ext (map_fst_prod P.val (SB : Subgroup B))
  refine Functor.hext hobj ?_
  rintro P Q ⟨⟨g, hg⟩⟩
  exact mk_heq p (congrArg Obj.val (hobj P)) (congrArg Obj.val (hobj Q)) rfl _ _

section Mul
variable {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf' : PresFactors hα')
include hf'

lemma fnA_mul : fnA SB (α := α * α') = fnA SB (α := α') ⋙ fnA SB (α := α) := by
  have hobj : ∀ P : Obj p (SA : Subgroup A),
      (fnA SB (α := α * α')).obj P = (fnA SB (α := α') ⋙ fnA SB (α := α)).obj P := fun P => by
    apply Obj.ext
    change ((α.fn.obj (α'.fn.obj (prodObj SB P))).val).map (MonoidHom.fst A B) =
      ((α.fn.obj (prodObj SB (objA (α := α') P))).val).map (MonoidHom.fst A B)
    rw [obj_prodObj hα' hf' P]
  refine Functor.hext hobj ?_
  intro P Q ψ
  change HEq (projFst (α.fn.map (α'.fn.map (liftA SB ψ))))
    (projFst (α.fn.map (liftA SB ((fnA SB (α := α')).map ψ))))
  refine projFst_heq ?_ ?_ ?_
  · rw [obj_prodObj hα' hf' P]; rfl
  · rw [obj_prodObj hα' hf' Q]; rfl
  · exact Functor.map_heq' α.fn (obj_prodObj hα' hf' P) (obj_prodObj hα' hf' Q)
      (liftA_fnA hα' hf' ψ)

end Mul

section Laut
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)

variable (SB) in
/-- `α_A ∈ Aut(L(A))`. -/
noncomputable def lautA : LAut p (SA : Subgroup A) where
  hom := (fnA SB (α := α)).toCatHom
  inv := (fnA SB (α := α⁻¹)).toCatHom
  hom_inv_id := Cat.ext (by
    change fnA SB (α := α) ⋙ fnA SB (α := α⁻¹) = 𝟭 _
    rw [← fnA_mul (α := α⁻¹) hα hf, fnA_congr (inv_mul_cancel α), fnA_one])
  inv_hom_id := Cat.ext (by
    change fnA SB (α := α⁻¹) ⋙ fnA SB (α := α) = 𝟭 _
    rw [← fnA_mul (α := α) (inv_mem hα) (presFactors_inv hα hf), fnA_congr (mul_inv_cancel α), fnA_one])

lemma lautA_fn : (lautA SB hα hf).fn = fnA SB (α := α) := rfl

end Laut

section Mem
variable {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
  (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
  (hf : PresFactors hα)
include hf

lemma mem_objA {P : Obj p (SA : Subgroup A)} {y : A} :
    y ∈ (objA (α := α) P).val ↔ ∃ x, ∃ hx : x ∈ (SA : Subgroup A), x ∈ P.val ∧ bA hα x hx = y := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [obj_val_eq hα] at hr
    obtain ⟨hrS, hzX⟩ := (mem_bmap_iff (beta hα)).1 hr
    set z := (beta hα).symm ⟨r, hrS⟩ with hz_def
    have hrz : r = (((beta hα) z : _) : A × B) := by rw [hz_def, MulEquiv.apply_symm_apply]
    have hzP : (z : A × B).1 ∈ P.val := (show (z : A × B) ∈ P.val.prod (SB : Subgroup B) from hzX).1
    refine ⟨(z : A × B).1, z.2.1, hzP, ?_⟩
    rw [hrz, beta_apply]
    have h2 : ((betaFun hα z : _) : A × B) =
        (bA hα (z : A × B).1 (mem_prodSylow_fst z.2), bB hα (z : A × B).2 (mem_prodSylow_snd z.2)) :=
      betaFun_pair hα hf _ _ _ _
    rw [h2]; rfl
  · rintro ⟨x, hx, hxP, rfl⟩
    have hmem : ((x, 1) : A × B) ∈ (prodObj SB P).val := ⟨hxP, one_mem _⟩
    have := mem_bmap (β := beta hα) (⟨(x, 1), mem_prodSylow hx (one_mem _)⟩ : _) hmem
    rw [← obj_val_eq hα] at this
    exact ⟨_, this, rfl⟩

lemma fnA_map_mk {P : Obj p (SA : Subgroup A)} {x : A} (hxP : x ∈ P.val)
    (hx : x ∈ transporter P.val P.val) :
    ∃ hb : bA hα x (P.2.1 hxP) ∈ transporter (objA (α := α) P).val (objA (α := α) P).val,
      (fnA SB (α := α)).map (show P ⟶ P from Tame.mk p x hx) = Tame.mk p (bA hα x (P.2.1 hxP)) hb := by
  obtain ⟨hb, e⟩ := map_mk_delta hα (prodObj SB P) (x := (x, 1)) ⟨hxP, one_mem _⟩
  refine ⟨mem_transporter_self ((mem_objA hα hf).2 ⟨x, P.2.1 hxP, hxP, rfl⟩), ?_⟩
  change projFst (α.fn.map (show prodObj SB P ⟶ prodObj SB P from
    Tame.mk p ((x, 1) : A × B) (mem_transporter_self (show ((x, 1) : A × B) ∈ (prodObj SB P).val from
      ⟨hxP, one_mem _⟩)))) = _
  rw [e]
  rfl

/-- `α_A ∈ Aut_typ^I(L(A))`. -/
lemma lautA_mem : lautA SB hα hf ∈ autTypI p (SA : Subgroup A) := by
  refine ⟨fun P => ?_, fun P Q h => ?_⟩
  · rw [lautA_fn]
    ext m
    constructor
    · rintro ⟨_, ⟨x, hx, hxP, rfl⟩, rfl⟩
      obtain ⟨hb, e⟩ := fnA_map_mk hα hf hxP hx
      rw [e]
      exact ⟨_, hb, (mem_objA hα hf).2 ⟨x, P.2.1 hxP, hxP, rfl⟩, rfl⟩
    · rintro ⟨y, hy, hyP, rfl⟩
      obtain ⟨x, hxS, hxP, rfl⟩ := (mem_objA hα hf).1 hyP
      obtain ⟨hb, e⟩ := fnA_map_mk hα hf hxP (mem_transporter_self hxP)
      exact ⟨_, ⟨x, mem_transporter_self hxP, hxP, rfl⟩, e⟩
  · obtain ⟨h', e⟩ := hα.2 (prodObj SB P) (prodObj SB Q)
      (prod_mono h le_rfl : (prodObj SB P).val ≤ (prodObj SB Q).val)
    refine ⟨map_mono h', ?_⟩
    change projFst (α.fn.map (liftA SB (incl p _ h))) =
      (incl p _ (map_mono h') : objA (α := α) P ⟶ objA (α := α) Q)
    rw [liftA_incl, e]
    rfl

/-- `β(α_A) = β_A`. -/
lemma betaFun_lautA (x : (SA : Subgroup A)) :
    ((betaFun (lautA_mem hα hf) x : _) : A) = bA hα x x.2 := by
  have e1 := map_mk_top (lautA_mem hα hf) x
  obtain ⟨hb, e2⟩ := fnA_map_mk hα hf (P := topObj SA) x.2 (mem_transporter_self x.2)
  have e3 := e1.symm.trans e2
  exact beta_unique (lautA_mem hα hf) (betaFun (lautA_mem hα hf) x).2 (bA_mem hα x x.2) e3

end Mem

end AndersenOliverVentura.Tame

