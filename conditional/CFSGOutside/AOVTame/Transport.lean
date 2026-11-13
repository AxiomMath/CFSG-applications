import CFSGOutside.AOVTame.OutTyp

/-!
# AOV tameness: transporting `Out_typ` along isomorphisms of linking systems

An isomorphism of categories `E : L^c_S(G) ≅ L^c_{S'}(G')` which matches the subgroups
`δ_P(P)` induces `Out_typ(L^c_S(G)) ≃* Out_typ(L^c_{S'}(G'))`, `[α] ↦ [E α E⁻¹]`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G G' G'' : Type u} [Group G] [Group G'] [Group G''] (p : ℕ) [Fact p.Prime]
  {S : Subgroup G} {S' : Subgroup G'} {S'' : Subgroup G''}

/-- A functor between linking systems matching `δ_P(P)` with `δ_{F(P)}(F(P))`. -/
def IsoTyp (F : Obj p S ⥤ Obj p S') : Prop :=
  ∀ P : Obj p S, F.map '' deltaSet p S P = deltaSet p S' (F.obj P)

lemma IsoTyp.comp {F : Obj p S ⥤ Obj p S'} {F' : Obj p S' ⥤ Obj p S''} (hF : IsoTyp p F)
    (hF' : IsoTyp p F') : IsoTyp p (F ⋙ F') := fun P => by
  change (fun m => F'.map (F.map m)) '' _ = _
  rw [show (fun m : P ⟶ P => F'.map (F.map m)) = F'.map ∘ F.map from rfl, Set.image_comp, hF P,
    hF' (F.obj P)]
  rfl

lemma isIsotypical_iff_isoTyp (F : Obj p S ⥤ Obj p S) : IsIsotypical p S F ↔ IsoTyp p F := Iff.rfl

variable {p}

/-- An isomorphism of linking systems matching the subgroups `δ_P(P)` in both directions. -/
structure TypIso (E : Cat.of (Obj p S) ≅ Cat.of (Obj p S')) : Prop where
  hom : IsoTyp p E.hom.toFunctor
  inv : IsoTyp p E.inv.toFunctor

variable {E : Cat.of (Obj p S) ≅ Cat.of (Obj p S')}

lemma TypIso.conj_mem (hE : TypIso E) {x : End (Cat.of (Obj p S))} (hx : x ∈ typEquivs p S) :
    (E.inv ≫ x ≫ E.hom : End (Cat.of (Obj p S'))) ∈ typEquivs p S' := by
  obtain ⟨h₁, h₂⟩ := hx
  have eE : E.hom.toFunctor.IsEquivalence := (Cat.equivOfIso E).isEquivalence_functor
  have eE' : E.inv.toFunctor.IsEquivalence := (Cat.equivOfIso E.symm).isEquivalence_functor
  refine ⟨?_, ?_⟩
  · change (E.inv.toFunctor ⋙ x.toFunctor ⋙ E.hom.toFunctor).IsEquivalence
    exact inferInstance
  · change IsoTyp p (E.inv.toFunctor ⋙ x.toFunctor ⋙ E.hom.toFunctor)
    exact IsoTyp.comp p hE.inv (IsoTyp.comp p (show IsoTyp p x.toFunctor from h₂) hE.hom)

/-- Conjugation by `E` on isotypical self-equivalences, followed by the quotient map. -/
def TypIso.conjHom (hE : TypIso E) : typEquivs p S →* OutTyp p S' where
  toFun x := (natIsoCon p S').mk' ⟨E.inv ≫ x.1 ≫ E.hom, hE.conj_mem x.2⟩
  map_one' := by
    rw [← map_one (natIsoCon p S').mk']
    congr 1
    apply Subtype.ext
    change E.inv ≫ 𝟙 _ ≫ E.hom = 𝟙 _
    simp
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change E.inv ≫ (y.1 ≫ x.1) ≫ E.hom = (E.inv ≫ y.1 ≫ E.hom) ≫ (E.inv ≫ x.1 ≫ E.hom)
    simp

/-- `Out_typ(L) → Out_typ(L')`, `[α] ↦ [E α E⁻¹]`. -/
def TypIso.outTyp (hE : TypIso E) : OutTyp p S →* OutTyp p S' :=
  (natIsoCon p S).lift hE.conjHom (by
    rintro x y ⟨e⟩
    apply (natIsoCon p S').eq.2
    exact ⟨Functor.isoWhiskerLeft E.inv.toFunctor (Functor.isoWhiskerRight e E.hom.toFunctor)⟩)

lemma TypIso.outTyp_mk (hE : TypIso E) (x : typEquivs p S) :
    hE.outTyp ((natIsoCon p S).mk' x) =
      (natIsoCon p S').mk' ⟨E.inv ≫ x.1 ≫ E.hom, hE.conj_mem x.2⟩ := rfl

lemma TypIso.symm (hE : TypIso E) : TypIso E.symm := ⟨hE.inv, hE.hom⟩

lemma TypIso.outTyp_outTyp_symm (hE : TypIso E) (y : OutTyp p S') :
    hE.outTyp (hE.symm.outTyp y) = y := by
  obtain ⟨x, rfl⟩ := Con.mk'_surjective y
  rw [hE.symm.outTyp_mk, hE.outTyp_mk]
  congr 1
  apply Subtype.ext
  change E.inv ≫ (E.hom ≫ x.1 ≫ E.inv) ≫ E.hom = x.1
  simp

end AndersenOliverVentura.Tame
