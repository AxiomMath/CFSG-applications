import CFSGOutside.AOVTame.AutKer

/-!
# AOV tameness: AOV Lemma 1.14(a), surjectivity

Every isotypical self-equivalence of `L = L^c_S(G)` is naturally isomorphic to an element of
`Aut_typ^I(L)`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}

lemma isCentric_conjSub {S R : Subgroup G} (hR : IsCentric S R) {g : G} (hg : conjSub g R ≤ S) :
    IsCentric S (conjSub g R) := by
  refine ⟨hg, fun h hh => ?_⟩
  rw [conjSub_conjSub] at hh ⊢
  exact hR.2 _ hh

/-- Conjugating morphisms: `[h] ↦ [g' h g⁻¹] : gAg⁻¹ → g'Bg'⁻¹`. -/
def conjMor (g g' : G) {A B : Subgroup G} : Mor p A B → Mor p (conjSub g A) (conjSub g' B) :=
  Quotient.lift (fun h => mk p (g' * (h : G) * g⁻¹) (by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨h * x * (h : G)⁻¹, h.2 x hx, ?_⟩
      simp [mul_assoc]))
    (by
      rintro ⟨h, hh⟩ ⟨h', hh'⟩ (e : h⁻¹ * h' ∈ opCent p A)
      apply (mk_eq_mk p).2
      have := conj_mem_opCent_conjSub e g
      convert this using 1
      group)

@[simp] lemma conjMor_mk (g g' : G) {A B : Subgroup G} (h : G) (hh : h ∈ transporter A B) :
    conjMor (p := p) g g' (mk p h hh) = mk p (g' * h * g⁻¹) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨h * x * h⁻¹, hh x hx, by simp [mul_assoc]⟩) := rfl

variable (T) in
lemma equiv_obj_top (F : Obj p (T : Subgroup G) ⥤ Obj p (T : Subgroup G)) [F.IsEquivalence] :
    F.obj (topObj T) = topObj T := by
  let X := F.objPreimage (topObj T)
  let e : F.obj X ≅ topObj T := F.objObjPreimageIso (topObj T)
  obtain ⟨⟨g, hg⟩, -⟩ := Quotient.exists_rep (e.inv ≫ F.map (incl p (T : Subgroup G)
    (P := X) (Q := topObj T) X.2.1))
  apply Obj.ext
  apply Subgroup.eq_of_le_of_card_ge
  · exact (F.obj (topObj T)).2.1
  · have hle : conjSub g (T : Subgroup G) ≤ (F.obj (topObj T)).val :=
      fun _ ⟨x, hx, e⟩ => e ▸ hg x hx
    have := Subgroup.card_le_of_le hle
    rwa [card_conjSub] at this

/-- A full, faithful, inclusion-preserving endofunctor of `L^c_S(G)` is injective on objects. -/
lemma obj_injective_of_preservesIncl (B : Obj p (T : Subgroup G) ⥤ Obj p (T : Subgroup G))
    [B.Full] [B.Faithful] (hB : PreservesIncl p (T : Subgroup G) B) : Function.Injective B.obj := by
  have key : ∀ P Q : Obj p (T : Subgroup G), B.obj P = B.obj Q → P.val ≤ Q.val := by
    intro P Q hPQ
    have hle : (B.obj P).val ≤ (B.obj Q).val := le_of_eq (congrArg Obj.val hPQ)
    let ψ : P ⟶ Q := B.preimage (incl p (T : Subgroup G) hle)
    obtain ⟨hP, eP⟩ := hB P (topObj T) P.2.1
    obtain ⟨hQ, eQ⟩ := hB Q (topObj T) Q.2.1
    have h1 : ψ ≫ incl p (T : Subgroup G) (P := Q) (Q := topObj T) Q.2.1 =
        incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1 := by
      apply B.map_injective
      rw [B.map_comp, B.map_preimage, eQ, eP]
      exact mk_congr p (by group) _ _
    obtain ⟨⟨g, hg⟩, eg⟩ := Quotient.exists_rep ψ
    rw [← eg] at h1
    have h2 := (mk_eq_mk p).1 h1
    have hgC : g ∈ centralizer (P.val : Set G) := by
      have : g⁻¹ ∈ opCent p P.val := by simpa using h2
      have := opCent_le_centralizer p _ (inv_mem this)
      simpa using this
    intro x hx
    have h3 := hg x hx
    have : g * x * g⁻¹ = x := by
      rw [← mem_centralizer_iff.1 hgC x hx]; group
    rwa [this] at h3
  intro P Q hPQ
  exact Obj.ext (le_antisymm (key P Q hPQ) (key Q P hPQ.symm))

section Construction

variable (F : Obj p (T : Subgroup G) ⥤ Obj p (T : Subgroup G)) [F.IsEquivalence]

lemma exists_gP (P : Obj p (T : Subgroup G)) :
    ∃ (g : G) (hg : g ∈ transporter (F.obj P).val (F.obj (topObj T)).val),
      F.map (incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1) = mk p g hg := by
  obtain ⟨⟨g, hg⟩, e⟩ := Quotient.exists_rep
    (F.map (incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1))
  exact ⟨g, hg, e.symm⟩

/-- `F(ι_P^S) = [g_P]`. -/
noncomputable def gP (P : Obj p (T : Subgroup G)) : G := (exists_gP F P).choose

lemma gP_mem (P : Obj p (T : Subgroup G)) :
    gP F P ∈ transporter (F.obj P).val (F.obj (topObj T)).val := (exists_gP F P).choose_spec.choose

lemma gP_spec (P : Obj p (T : Subgroup G)) :
    F.map (incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1) = mk p (gP F P) (gP_mem F P) :=
  (exists_gP F P).choose_spec.choose_spec

lemma gP_le (P : Obj p (T : Subgroup G)) : conjSub (gP F P) (F.obj P).val ≤ T := by
  rintro _ ⟨x, hx, rfl⟩
  have := gP_mem F P x hx
  rw [equiv_obj_top T F] at this
  exact this

/-- The object map `P ↦ g_P F(P) g_P⁻¹`. -/
noncomputable def betaObj (P : Obj p (T : Subgroup G)) : Obj p (T : Subgroup G) :=
  ⟨conjSub (gP F P) (F.obj P).val, isCentric_conjSub (F.obj P).2 (gP_le F P)⟩

/-- The functor `β = ω F ω⁻¹` with `ω(P) = [g_P] : F(P) → β(P)`. -/
noncomputable def betaFunctor : Obj p (T : Subgroup G) ⥤ Obj p (T : Subgroup G) where
  obj := betaObj F
  map {P Q} ψ := (conjMor (gP F P) (gP F Q) (F.map ψ) : Mor p (betaObj F P).val (betaObj F Q).val)
  map_id P := by
    rw [F.map_id]
    show conjMor (p := p) (gP F P) (gP F P) (mk p 1 _) = mk p 1 _
    rw [conjMor_mk]
    exact mk_congr p (by group) _ _
  map_comp {P Q R} f g := by
    rw [F.map_comp]
    obtain ⟨⟨a, ha⟩, ea⟩ := Quotient.exists_rep (F.map f)
    obtain ⟨⟨b, hb⟩, eb⟩ := Quotient.exists_rep (F.map g)
    rw [← ea, ← eb]
    show conjMor (p := p) (gP F P) (gP F R) (comp p (mk p b hb) (mk p a ha)) =
      comp p (conjMor (p := p) (gP F Q) (gP F R) (mk p b hb))
        (conjMor (p := p) (gP F P) (gP F Q) (mk p a ha))
    rw [comp_mk, conjMor_mk, conjMor_mk, conjMor_mk]
    exact mk_congr p (by group) _ _

lemma gP_mem_conj (P : Obj p (T : Subgroup G)) :
    gP F P ∈ transporter (F.obj P).val (betaObj F P).val := fun x hx => ⟨x, hx, rfl⟩

lemma gP_inv_mem_conj (P : Obj p (T : Subgroup G)) :
    (gP F P)⁻¹ ∈ transporter (betaObj F P).val (F.obj P).val := by
  rintro _ ⟨x, hx, rfl⟩; simpa [mul_assoc] using hx

/-- The natural isomorphism `ω : F ≅ β`, `ω(P) = [g_P]`. -/
noncomputable def omegaIso : F ≅ betaFunctor F :=
  NatIso.ofComponents
    (fun P => ⟨mk p (gP F P) (gP_mem_conj F P), mk p (gP F P)⁻¹ (gP_inv_mem_conj F P),
      mk_congr p (inv_mul_cancel _) _ _, mk_congr p (mul_inv_cancel _) _ _⟩)
    (by
      intro P Q ψ
      obtain ⟨⟨h, hh⟩, eh⟩ := Quotient.exists_rep (F.map ψ)
      show comp p (mk p (gP F Q) _) (F.map ψ) =
        comp p (conjMor (p := p) (gP F P) (gP F Q) (F.map ψ)) (mk p (gP F P) _)
      rw [← eh]
      show comp p (mk p (gP F Q) _) (mk p h hh) =
        comp p (conjMor (p := p) (gP F P) (gP F Q) (mk p h hh)) (mk p (gP F P) _)
      rw [conjMor_mk]
      exact mk_congr p (by group) _ _)

lemma betaFunctor_isIsotypical (hF : IsIsotypical p (T : Subgroup G) F) :
    IsIsotypical p (T : Subgroup G) (betaFunctor F) := by
  intro P
  have e : (betaFunctor F).map = fun ψ : P ⟶ P =>
      (conjMor (gP F P) (gP F P) (F.map ψ) : Mor p (betaObj F P).val (betaObj F P).val) := rfl
  ext m
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    have : F.map ψ ∈ deltaSet p (T : Subgroup G) (F.obj P) := hF P ▸ ⟨ψ, hψ, rfl⟩
    obtain ⟨x, hx, hxP, ex⟩ := this
    refine ⟨gP F P * x * (gP F P)⁻¹, mem_transporter_self ⟨x, hxP, rfl⟩, ⟨x, hxP, rfl⟩, ?_⟩
    change conjMor (p := p) (gP F P) (gP F P) (F.map ψ) = _
    rw [ex, conjMor_mk]
    rfl
  · rintro ⟨y, hy, ⟨x, hxP, rfl⟩, rfl⟩
    have : (mk p x (mem_transporter_self hxP) : F.obj P ⟶ F.obj P) ∈
        deltaSet p (T : Subgroup G) (F.obj P) := ⟨x, _, hxP, rfl⟩
    rw [← hF P] at this
    obtain ⟨ψ, hψ, eψ⟩ := this
    refine ⟨ψ, hψ, ?_⟩
    change conjMor (p := p) (gP F P) (gP F P) (F.map ψ) = _
    rw [eψ, conjMor_mk]
    rfl

lemma betaFunctor_preservesIncl : PreservesIncl p (T : Subgroup G) (betaFunctor F) := by
  intro P Q hPQ
  obtain ⟨⟨h, hh⟩, eh⟩ := Quotient.exists_rep (F.map (incl p (T : Subgroup G) (P := P) (Q := Q) hPQ))
  have hcomp : incl p (T : Subgroup G) (P := P) (Q := Q) hPQ ≫
      incl p (T : Subgroup G) (P := Q) (Q := topObj T) Q.2.1 =
      incl p (T : Subgroup G) (P := P) (Q := topObj T) P.2.1 := mk_congr p (by group) _ _
  have hF := congrArg F.map hcomp
  rw [F.map_comp, gP_spec, gP_spec, ← eh] at hF
  have hc : (gP F Q * h)⁻¹ * gP F P ∈ opCent p (F.obj P).val := (mk_eq_mk p).1 hF
  set k := gP F Q * h * (gP F P)⁻¹ with hk
  have hkc : k ∈ opCent p (betaObj F P).val := by
    have := conj_mem_opCent_conjSub (inv_mem hc) (gP F P)
    convert this using 1
    · rfl
    · rw [hk]; group
  have hkt : k ∈ transporter (betaObj F P).val (betaObj F Q).val := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨h * x * h⁻¹, hh x hx, ?_⟩
    simp only [hk, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hkC := opCent_le_centralizer p _ hkc
  have hle : (betaObj F P).val ≤ (betaObj F Q).val := by
    intro y hy
    have h1 := hkt y hy
    have h2 := mem_centralizer_iff.1 hkC y hy
    have : k * y * k⁻¹ = y := by rw [← h2]; group
    rwa [this] at h1
  refine ⟨hle, ?_⟩
  change conjMor (p := p) (gP F P) (gP F Q) (F.map (incl p (T : Subgroup G) hPQ)) = _
  rw [← eh]
  change conjMor (p := p) (gP F P) (gP F Q) (mk p h hh) = _
  rw [conjMor_mk]
  apply (mk_eq_mk p).2
  have := inv_mem hkc
  simp only [hk, mul_inv_rev, inv_inv, mul_one] at this ⊢
  convert this using 2 <;> first | rfl | group

end Construction

/-- **AOV Lemma 1.14(a), surjectivity.** Every isotypical self-equivalence of `L^c_S(G)` is
naturally isomorphic to an element of `Aut_typ^I(L^c_S(G))`. -/
theorem exists_autTypI_iso (F : Obj p (T : Subgroup G) ⥤ Obj p (T : Subgroup G)) [F.IsEquivalence]
    (hF : IsIsotypical p (T : Subgroup G) F) :
    ∃ α ∈ autTypI p (T : Subgroup G), Nonempty (F ≅ α.fn) := by
  haveI : (betaFunctor F).IsEquivalence := Functor.isEquivalence_of_iso (omegaIso F)
  haveI : (betaFunctor F).IsIso :=
    ⟨inferInstance, inferInstance, Finite.injective_iff_bijective.1
      (obj_injective_of_preservesIncl _ (betaFunctor_preservesIncl F))⟩
  let I := (betaFunctor F).asIsomorphism
  let α : LAut p (T : Subgroup G) :=
    ⟨I.functor.toCatHom, I.inverse.toCatHom, Cat.ext I.unit_eq.symm, Cat.ext I.counit_eq⟩
  exact ⟨α, ⟨betaFunctor_isIsotypical F hF, betaFunctor_preservesIncl F⟩, ⟨omegaIso F⟩⟩

end AndersenOliverVentura.Tame
