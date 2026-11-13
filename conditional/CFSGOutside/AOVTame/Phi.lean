import CFSGOutside.AOVTame.Product
import CFSGOutside.AOVTame.Bmap
import CFSGOutside.AOVTame.Surj

/-!
# AOV tameness: `α ↦ α × Id` from `Aut_typ^I(L(A))` to `Aut_typ^I(L(A × B))`

The construction `Φ(α, Id)` in the proof of AOV Theorem 3.8.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

lemma isCentric_bmap {G : Type*} [Group G] [Finite G] {T : Sylow p G}
    (β : (T : Subgroup G) ≃* (T : Subgroup G)) {P : Subgroup G} (hP : IsCentric (T : Subgroup G) P)
    (hfus : ∀ g : G, conjSub g (bmap β P) ≤ T →
      ∃ k : G, conjSub k P ≤ T ∧ bmap β (conjSub k P) = conjSub g (bmap β P)) :
    IsCentric (T : Subgroup G) (bmap β P) := by
  refine ⟨bmap_le β P, fun g hg => ?_⟩
  obtain ⟨k, hk, e⟩ := hfus g hg
  rw [← e, ← bmap_centralizer_inf β hk, ← bmap_inf_centralizer β hk, hP.2 k hk]

variable {α : LAut p (SA : Subgroup A)} (hα : α ∈ autTypI p (SA : Subgroup A))

variable (SB) in
/-- `β × Id` on `S_A × S_B`. -/
noncomputable def bX : ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) ≃*
    ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  (MulEquiv.subgroupCongr (coe_prodSylow SA SB)).trans ((prodEquiv (SA : Subgroup A) (SB : Subgroup B)).trans
    (((beta hα).prodCongr (MulEquiv.refl _)).trans
      ((prodEquiv (SA : Subgroup A) (SB : Subgroup B)).symm.trans
        (MulEquiv.subgroupCongr (coe_prodSylow SA SB)).symm)))

include hα in
lemma mem_bmap_bX_iff {P : Subgroup (A × B)} {z : A × B} :
    z ∈ bmap (bX SB hα) P ↔ ∃ x ∈ P, ∃ hx : x.1 ∈ (SA : Subgroup A), x.2 ∈ (SB : Subgroup B) ∧
      z = ((betaFun hα ⟨x.1, hx⟩ : A), x.2) := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, x.2.1, x.2.2, rfl⟩
  · rintro ⟨x, hx, h1, h2, rfl⟩
    exact ⟨_, ⟨⟨x, h1, h2⟩, hx, rfl⟩, rfl⟩

include hα in
lemma bmap_bX_fst {P : Subgroup (A × B)} (hP : P ≤ (SA : Subgroup A).prod SB) :
    (bmap (bX SB hα) P).map (MonoidHom.fst A B) = bmap (beta hα) (P.map (MonoidHom.fst A B)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, h1, -, rfl⟩ := (mem_bmap_bX_iff hα).1 hz
    exact mem_bmap ⟨x.1, h1⟩ ⟨x, hx, rfl⟩
  · rintro ⟨_, ⟨⟨a, ha⟩, ⟨x, hx, hxa⟩, rfl⟩, rfl⟩
    refine ⟨((betaFun hα ⟨a, ha⟩ : A), x.2), (mem_bmap_bX_iff hα).2 ⟨x, hx, (hP hx).1, (hP hx).2, ?_⟩, rfl⟩
    simp only [MonoidHom.coe_fst] at hxa
    subst hxa
    rfl

include hα in
lemma bmap_bX_snd {P : Subgroup (A × B)} (hP : P ≤ (SA : Subgroup A).prod SB) :
    (bmap (bX SB hα) P).map (MonoidHom.snd A B) = P.map (MonoidHom.snd A B) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, h1, -, rfl⟩ := (mem_bmap_bX_iff hα).1 hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, (mem_bmap_bX_iff hα).2 ⟨x, hx, (hP hx).1, (hP hx).2, rfl⟩, rfl⟩

include hα in
/-- `β × Id` is fusion preserving on conjugates of centric subgroups. -/
lemma bX_fusion {P : Subgroup (A × B)}
    (hP : IsCentric ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) P) (g : A × B)
    (hg : conjSub g (bmap (bX SB hα) P) ≤ (prodSylow SA SB : Sylow p (A × B))) :
    ∃ k : A × B, conjSub k P ≤ (prodSylow SA SB : Sylow p (A × B)) ∧
      bmap (bX SB hα) (conjSub k P) = conjSub g (bmap (bX SB hα) P) := by
  have hPS : P ≤ (SA : Subgroup A).prod SB := hP.1
  let Q₁ : Obj p (SA : Subgroup A) := ⟨P.map (MonoidHom.fst A B), isCentric_fst hP⟩
  have hQ₁ : (α.fn.obj Q₁).val = bmap (beta hα) (P.map (MonoidHom.fst A B)) := obj_val_eq hα Q₁
  have hle₁ : conjSub g.1 (α.fn.obj Q₁).val ≤ SA := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hQ₁, ← bmap_bX_fst hα hPS] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact (hg ⟨z, hz, rfl⟩).1
  let R' : Obj p (SA : Subgroup A) :=
    ⟨conjSub g.1 (α.fn.obj Q₁).val, isCentric_conjSub (α.fn.obj Q₁).2 hle₁⟩
  have hg₁ : g.1 ∈ transporter (α.fn.obj Q₁).val R'.val := fun y hy => ⟨y, hy, rfl⟩
  obtain ⟨⟨k₁, hk₁⟩, ek⟩ := Quotient.exists_rep ((α⁻¹).fn.map (show α.fn.obj Q₁ ⟶ R' from mk p g.1 hg₁))
  have hrel := map_mk_conj' (inv_mem hα) hg₁ hk₁ ek.symm
  have hk₁' : k₁ ∈ transporter Q₁.val (α⁻¹.fn.obj R').val := by
    have := hk₁; rwa [LAut.obj_obj_inv] at this
  -- the key identity `β(k₁ x k₁⁻¹) = g₁ β(x) g₁⁻¹`
  have key : ∀ (x : A) (hx : x ∈ P.map (MonoidHom.fst A B)),
      (betaFun hα ⟨k₁ * x * k₁⁻¹, (α⁻¹.fn.obj R').2.1 (hk₁' x hx)⟩ : A) =
        g.1 * betaFun hα ⟨x, Q₁.2.1 hx⟩ * g.1⁻¹ := by
    intro x hx
    have hy : (betaFun hα ⟨x, Q₁.2.1 hx⟩ : A) ∈ (α.fn.obj Q₁).val := by
      rw [hQ₁]; exact mem_bmap ⟨x, Q₁.2.1 hx⟩ hx
    have h1 := hrel _ hy
    have h2 : (betaFun (inv_mem hα) ⟨_, (α.fn.obj Q₁).2.1 hy⟩ : A) = x := by
      have := betaFun_inv_aut hα ⟨x, Q₁.2.1 hx⟩
      exact congrArg Subtype.val this
    rw [h2] at h1
    have h3 : (⟨k₁ * x * k₁⁻¹, (α⁻¹.fn.obj R').2.1 (hk₁' x hx)⟩ : (SA : Subgroup A)) =
        betaFun (inv_mem hα) ⟨g.1 * betaFun hα ⟨x, Q₁.2.1 hx⟩ * g.1⁻¹, R'.2.1 (hg₁ _ hy)⟩ :=
      Subtype.ext h1
    rw [h3, betaFun_inv_aut' hα]
  refine ⟨(k₁, g.2), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(α⁻¹.fn.obj R').2.1 (hk₁' _ ⟨x, hx, rfl⟩), ?_⟩
    have := (hg ⟨_, (mem_bmap_bX_iff hα).2 ⟨x, hx, (hPS hx).1, (hPS hx).2, rfl⟩, rfl⟩).2
    exact this
  · ext z
    rw [mem_bmap_bX_iff hα]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, h1, h2, rfl⟩
      refine ⟨_, (mem_bmap_bX_iff hα).2 ⟨x, hx, (hPS hx).1, (hPS hx).2, rfl⟩, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      refine Prod.ext ?_ rfl
      simp only [Prod.fst_mul, Prod.fst_inv]
      exact (key x.1 ⟨x, hx, rfl⟩).symm
    · rintro ⟨_, hw, rfl⟩
      obtain ⟨x, hx, h1, h2, rfl⟩ := (mem_bmap_bX_iff hα).1 hw
      refine ⟨(k₁, g.2) * x * (k₁, g.2)⁻¹, ⟨x, hx, rfl⟩,
        (α⁻¹.fn.obj R').2.1 (hk₁' _ ⟨x, hx, rfl⟩), ?_, ?_⟩
      · have := (hg ⟨_, (mem_bmap_bX_iff hα).2 ⟨x, hx, h1, h2, rfl⟩, rfl⟩).2
        exact this
      · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        refine Prod.ext ?_ rfl
        simp only [Prod.fst_mul, Prod.fst_inv]
        exact (key x.1 ⟨x, hx, rfl⟩).symm

variable (SB) in
/-- The object `(β × Id)(P)`. -/
noncomputable def phiObj (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  ⟨bmap (bX SB hα) P.val, isCentric_bmap (bX SB hα) P.2 (fun g hg => bX_fusion hα P.2 g hg)⟩

/-- The first projection of an object of `L(A × B)`, an object of `L(A)`. -/
def proj₁ (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    Obj p (SA : Subgroup A) :=
  ⟨P.val.map (MonoidHom.fst A B), isCentric_fst P.2⟩

include hα in
lemma phiObj_fst (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    (phiObj SB hα P).val.map (MonoidHom.fst A B) = (α.fn.obj (proj₁ P)).val := by
  rw [obj_val_eq hα]; exact bmap_bX_fst hα P.2.1

include hα in
lemma phiObj_snd (P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))) :
    (phiObj SB hα P).val.map (MonoidHom.snd A B) = P.val.map (MonoidHom.snd A B) :=
  bmap_bX_snd hα P.2.1

include hα in
lemma phi_transporter {P Q : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    {g : A × B} (hg : g ∈ transporter P.val Q.val) {h : A}
    (hh : h ∈ transporter (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
    (e : α.fn.map (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) = mk p h hh) :
    ((h, g.2) : A × B) ∈ transporter (phiObj SB hα P).val (phiObj SB hα Q).val := by
  intro z hz
  obtain ⟨x, hx, h1, h2, rfl⟩ := (mem_bmap_bX_iff hα).1 hz
  have hrel := map_mk_conj' hα (mem_transporter_fst hg) hh e x.1 ⟨x, hx, rfl⟩
  have hgx : g * x * g⁻¹ ∈ Q.val := hg x hx
  refine (mem_bmap_bX_iff hα).2 ⟨g * x * g⁻¹, hgx, (Q.2.1 hgx).1, (Q.2.1 hgx).2, ?_⟩
  refine Prod.ext ?_ (by simp)
  simp only [Prod.fst_mul, Prod.fst_inv]
  exact hrel

variable (SB) in
/-- `Φ(α, Id)` on morphisms: `[(g₁, g₂)] ↦ [(h₁, g₂)]` where `α([g₁]) = [h₁]`. -/
noncomputable def phiMor {P Q : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (ψ : P ⟶ Q) : phiObj SB hα P ⟶ phiObj SB hα Q :=
  let g := (Quotient.out (ψ : Mor p P.val Q.val) : transporter P.val Q.val)
  let m : Mor p (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val :=
    α.fn.map (show proj₁ P ⟶ proj₁ Q from mk p (g : A × B).1 (mem_transporter_fst g.2))
  let h := (Quotient.out m : transporter (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
  mk p ((h : A), (g : A × B).2) (phi_transporter hα g.2 h.2 (Quotient.out_eq m).symm)

include hα in
lemma phiMor_mk {P Q : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    {g : A × B} (hg : g ∈ transporter P.val Q.val) {h : A}
    (hh : h ∈ transporter (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
    (e : α.fn.map (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) = mk p h hh) :
    phiMor SB hα (show P ⟶ Q from mk p g hg) = mk p (h, g.2) (phi_transporter hα hg hh e) := by
  set ψ : P ⟶ Q := mk p g hg
  set g' := (Quotient.out (ψ : Mor p P.val Q.val) : transporter P.val Q.val)
  have hg' : (mk p (g' : A × B) g'.2 : P ⟶ Q) = ψ := Quotient.out_eq ψ
  have hc : (g' : A × B)⁻¹ * g ∈ opCent p P.val := (mk_eq_mk p).1 hg'
  -- the first components agree in `L(A)`
  have h1 : (show proj₁ P ⟶ proj₁ Q from mk p (g' : A × B).1 (mem_transporter_fst g'.2)) =
      (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) :=
    (mk_eq_mk p).2 (by
      have := opCent_fst hc
      simp only [Prod.fst_mul, Prod.fst_inv] at this
      exact this)
  set m : Mor p (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val :=
    α.fn.map (show proj₁ P ⟶ proj₁ Q from mk p (g' : A × B).1 (mem_transporter_fst g'.2))
  set h' := (Quotient.out m : transporter (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
  have hm : (mk p (h' : A) h'.2 : α.fn.obj (proj₁ P) ⟶ α.fn.obj (proj₁ Q)) = mk p h hh := by
    rw [show (mk p (h' : A) h'.2 : α.fn.obj (proj₁ P) ⟶ α.fn.obj (proj₁ Q)) = m from Quotient.out_eq m,
      ← e]
    exact congrArg α.fn.map h1
  have hc1 : (h' : A)⁻¹ * h ∈ opCent p ((phiObj SB hα P).val.map (MonoidHom.fst A B)) := by
    rw [phiObj_fst hα]; exact (mk_eq_mk p).1 hm
  have hc2 : ((g' : A × B).2)⁻¹ * g.2 ∈ opCent p ((phiObj SB hα P).val.map (MonoidHom.snd A B)) := by
    rw [phiObj_snd hα]; simpa using opCent_snd hc
  apply (mk_eq_mk p).2
  have := opCent_pair hc1 hc2
  simpa using this

variable (SB) in
/-- The functor `Φ(α, Id) : L(A × B) → L(A × B)`. -/
noncomputable def phiFunctor :
    Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) ⥤
      Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) where
  obj := phiObj SB hα
  map := phiMor SB hα
  map_id P := by
    have e : α.fn.map (show proj₁ P ⟶ proj₁ P from mk p ((1 : A × B).1)
        (mem_transporter_fst (one_mem_transporter le_rfl))) = mk p 1 (one_mem_transporter le_rfl) :=
      α.fn.map_id (proj₁ P)
    exact (phiMor_mk hα (one_mem_transporter le_rfl) _ e).trans (mk_congr p rfl _ _)
  map_comp {P Q R} f f' := by
    obtain ⟨⟨g, hg⟩, rfl⟩ := Quotient.exists_rep (f : Mor p P.val Q.val)
    obtain ⟨⟨g', hg'⟩, rfl⟩ := Quotient.exists_rep (f' : Mor p Q.val R.val)
    obtain ⟨⟨h, hh⟩, eh⟩ := Quotient.exists_rep (α.fn.map (show proj₁ P ⟶ proj₁ Q from
      mk p g.1 (mem_transporter_fst hg)) : Mor p (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
    obtain ⟨⟨h', hh'⟩, eh'⟩ := Quotient.exists_rep (α.fn.map (show proj₁ Q ⟶ proj₁ R from
      mk p g'.1 (mem_transporter_fst hg')) : Mor p (α.fn.obj (proj₁ Q)).val (α.fn.obj (proj₁ R)).val)
    have e₁ := phiMor_mk hα hg hh eh.symm
    have e₂ := phiMor_mk hα hg' hh' eh'.symm
    have hcomp : α.fn.map (show proj₁ P ⟶ proj₁ R from mk p (g' * g).1
        (mem_transporter_fst (mul_mem_transporter hg' hg))) =
        mk p (h' * h) (mul_mem_transporter hh' hh) := by
      have : (show proj₁ P ⟶ proj₁ R from mk p (g' * g).1
          (mem_transporter_fst (mul_mem_transporter hg' hg))) =
          (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) ≫
            (show proj₁ Q ⟶ proj₁ R from mk p g'.1 (mem_transporter_fst hg')) := rfl
      rw [this, Functor.map_comp]
      change comp p (α.fn.map _) (α.fn.map _) = _
      rw [← eh, ← eh']
      rfl
    have e₃ := phiMor_mk hα (mul_mem_transporter hg' hg) _ hcomp
    change phiMor SB hα (mk p (g' * g) (mul_mem_transporter hg' hg)) =
      comp p (phiMor SB hα (mk p g' hg')) (phiMor SB hα (mk p g hg))
    rw [e₁, e₂, e₃]
    exact mk_congr p rfl _ _

include hα in
lemma phiFunctor_isIsotypical :
    IsIsotypical p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) (phiFunctor SB hα) := by
  intro P
  ext m
  constructor
  · rintro ⟨_, ⟨x, hx, hxP, rfl⟩, rfl⟩
    obtain ⟨hb, e⟩ := map_mk_delta hα (proj₁ P) (x := x.1) ⟨x, hxP, rfl⟩
    have := phiMor_mk hα (P := P) (Q := P) hx (mem_transporter_self hb) e
    refine ⟨_, mem_transporter_self ((mem_bmap_bX_iff hα).2 ⟨x, hxP, (P.2.1 hxP).1,
      (P.2.1 hxP).2, rfl⟩), (mem_bmap_bX_iff hα).2 ⟨x, hxP, (P.2.1 hxP).1, (P.2.1 hxP).2, rfl⟩, ?_⟩
    exact this
  · rintro ⟨z, hz, hzP, rfl⟩
    obtain ⟨x, hxP, h1, h2, rfl⟩ := (mem_bmap_bX_iff hα).1 hzP
    obtain ⟨hb, e⟩ := map_mk_delta hα (proj₁ P) (x := x.1) ⟨x, hxP, rfl⟩
    refine ⟨mk p x (mem_transporter_self hxP), ⟨x, _, hxP, rfl⟩, ?_⟩
    exact phiMor_mk hα (P := P) (Q := P) (mem_transporter_self hxP) (mem_transporter_self hb) e

include hα in
lemma phiFunctor_preservesIncl :
    PreservesIncl p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) (phiFunctor SB hα) := by
  intro P Q hPQ
  obtain ⟨hle, e⟩ := hα.2 (proj₁ P) (proj₁ Q) (map_mono hPQ)
  refine ⟨bmap_mono _ hPQ, ?_⟩
  exact phiMor_mk hα (P := P) (Q := Q) (one_mem_transporter hPQ) (one_mem_transporter hle) e

include hα in
lemma phiFunctor_map_injective {P Q : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    {f f' : P ⟶ Q} (h : (phiFunctor SB hα).map f = (phiFunctor SB hα).map f') : f = f' := by
  obtain ⟨⟨g, hg⟩, rfl⟩ := Quotient.exists_rep (f : Mor p P.val Q.val)
  obtain ⟨⟨g', hg'⟩, rfl⟩ := Quotient.exists_rep (f' : Mor p P.val Q.val)
  obtain ⟨⟨k, hk⟩, ek⟩ := Quotient.exists_rep (α.fn.map (show proj₁ P ⟶ proj₁ Q from
    mk p g.1 (mem_transporter_fst hg)) : Mor p (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
  obtain ⟨⟨k', hk'⟩, ek'⟩ := Quotient.exists_rep (α.fn.map (show proj₁ P ⟶ proj₁ Q from
    mk p g'.1 (mem_transporter_fst hg')) : Mor p (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val)
  change phiMor SB hα (mk p g hg) = phiMor SB hα (mk p g' hg') at h
  rw [phiMor_mk hα hg hk ek.symm, phiMor_mk hα hg' hk' ek'.symm] at h
  have hc := (mk_eq_mk p).1 h
  have hc1 := opCent_fst hc
  have hc2 := opCent_snd hc
  rw [phiObj_fst hα] at hc1
  rw [phiObj_snd hα] at hc2
  simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv] at hc1 hc2
  have hm : (mk p k hk : α.fn.obj (proj₁ P) ⟶ α.fn.obj (proj₁ Q)) = mk p k' hk' := (mk_eq_mk p).2 hc1
  have hm' := ek.symm.trans (hm.trans ek')
  have h1 := (mk_eq_mk p).1 (LAut.map_injective α hm')
  apply (mk_eq_mk p).2
  have := opCent_pair (P := P.val) h1 hc2
  convert this using 1

include hα in
lemma phiFunctor_obj_injective : Function.Injective (phiFunctor SB hα).obj := by
  intro P Q h
  exact Obj.ext (bmap_injOn _ P.2.1 Q.2.1 (congrArg Obj.val h))

include hα in
lemma phiFunctor_map_surjective {P Q : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (m : (phiFunctor SB hα).obj P ⟶ (phiFunctor SB hα).obj Q) :
    ∃ f : P ⟶ Q, (phiFunctor SB hα).map f = m := by
  haveI : α.fn.Full := (Cat.equivOfIso α).full_functor
  obtain ⟨⟨k, hk⟩, rfl⟩ := Quotient.exists_rep
    (m : Mor p (phiObj SB hα P).val (phiObj SB hα Q).val)
  have hk' : k ∈ transporter (phiObj SB hα P).val (phiObj SB hα Q).val := hk
  have hk₁ : k.1 ∈ transporter (α.fn.obj (proj₁ P)).val (α.fn.obj (proj₁ Q)).val := by
    have := mem_transporter_fst hk'
    rwa [phiObj_fst hα, phiObj_fst hα] at this
  let n₁ : proj₁ P ⟶ proj₁ Q := α.fn.preimage (mk p k.1 hk₁)
  obtain ⟨⟨g₁, hg₁⟩, en⟩ := Quotient.exists_rep (n₁ : Mor p (proj₁ P).val (proj₁ Q).val)
  have e : α.fn.map (show proj₁ P ⟶ proj₁ Q from mk p g₁ hg₁) = mk p k.1 hk₁ := by
    change α.fn.map (⟦⟨g₁, hg₁⟩⟧ : proj₁ P ⟶ proj₁ Q) = _
    rw [en]; exact α.fn.map_preimage _
  have hrel := map_mk_conj' hα hg₁ hk₁ e
  have hg : ((g₁, k.2) : A × B) ∈ transporter P.val Q.val := by
    intro x hx
    have hz : ((betaFun hα ⟨x.1, (P.2.1 hx).1⟩ : A), x.2) ∈ (phiObj SB hα P).val :=
      (mem_bmap_bX_iff hα).2 ⟨x, hx, (P.2.1 hx).1, (P.2.1 hx).2, rfl⟩
    obtain ⟨y, hy, h1, h2, ey⟩ := (mem_bmap_bX_iff hα).1 (hk' _ hz)
    have ef := congrArg Prod.fst ey
    have es := congrArg Prod.snd ey
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv] at ef es
    rw [hrel x.1 ⟨x, hx, rfl⟩] at ef
    have ef' := betaFun_injective hα (Subtype.ext ef)
    have : ((g₁, k.2) : A × B) * x * (g₁, k.2)⁻¹ = y := by
      refine Prod.ext ?_ ?_
      · simpa using congrArg Subtype.val ef'
      · simpa using es
    rw [this]; exact hy
  refine ⟨mk p (g₁, k.2) hg, ?_⟩
  exact (phiMor_mk hα hg hk₁ e).trans (mk_congr p rfl _ _)

include hα in
lemma phiFunctor_isIso : (phiFunctor SB hα).IsIso where
  faithful := ⟨fun h => phiFunctor_map_injective hα h⟩
  full := ⟨fun m => phiFunctor_map_surjective hα m⟩
  bijective_obj := Finite.injective_iff_bijective.1 (phiFunctor_obj_injective hα)

variable (SB) in
/-- `Φ(α, Id) ∈ Aut_typ^I(L(A × B))`. -/
noncomputable def phiAut : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  haveI := phiFunctor_isIso (SB := SB) hα
  let I := (phiFunctor SB hα).asIsomorphism
  ⟨I.functor.toCatHom, I.inverse.toCatHom, Cat.ext I.unit_eq.symm, Cat.ext I.counit_eq⟩

lemma phiAut_fn : (phiAut SB hα).fn = phiFunctor SB hα := rfl

include hα in
lemma phiAut_mem : phiAut SB hα ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) :=
  ⟨phiFunctor_isIsotypical hα, phiFunctor_preservesIncl hα⟩

end AndersenOliverVentura.Tame
