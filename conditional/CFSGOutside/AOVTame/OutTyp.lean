import CFSGOutside.AOVTame.MapEquiv

/-!
# AOV tameness: `Out_typ(L)`, `κ_G` and tame fusion systems

`Out_typ(L)` (AOV Definition 1.13(c)) is the monoid of isotypical self-equivalences of
`L = L^c_S(G)` modulo natural isomorphism (a group by AOV Lemma 1.14(a); only its monoid structure
is used in the definition of tameness). `κ_G : Out(G) → Out_typ(L)` (AOV §2.2) sends the class of
`β ∈ Aut(G,S)` to the class of `P ↦ β(P)`, `[g] ↦ [β(g)]`; every class in `Out(G)` contains some
`β ∈ Aut(G,S)` (Frattini).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

variable {G : Type u} [Group G] (p : ℕ) [Fact p.Prime] (S : Subgroup G)

/-- The isotypical self-equivalences of `L^c_S(G)`. -/
def typEquivs : Submonoid (End (Cat.of (Obj p S))) where
  carrier := {F | F.toFunctor.IsEquivalence ∧ IsIsotypical p S F.toFunctor}
  one_mem' := ⟨(inferInstance : (𝟭 (Obj p S)).IsEquivalence), isIsotypical_id p S⟩
  mul_mem' := by
    rintro F F' ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩
    refine ⟨?_, h₂'.comp p S h₂⟩
    change (F'.toFunctor ⋙ F.toFunctor).IsEquivalence
    exact inferInstance

/-- Natural isomorphism of isotypical self-equivalences, as a monoid congruence. -/
def natIsoCon : Con (typEquivs p S) where
  r F F' := Nonempty (F.1.toFunctor ≅ F'.1.toFunctor)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩
  mul' := by
    intro w x y z hwx hyz
    obtain ⟨e⟩ := hwx
    obtain ⟨e'⟩ := hyz
    exact ⟨Functor.isoWhiskerLeft y.1.toFunctor e ≪≫ Functor.isoWhiskerRight e' x.1.toFunctor⟩

/-- `Out_typ(L^c_S(G))` (AOV Definition 1.13(c)): isotypical self-equivalences modulo natural
isomorphism. -/
abbrev OutTyp : Type u := (natIsoCon p S).Quotient

instance conj_range_normal (G : Type u) [Group G] : (MulAut.conj (G := G)).range.Normal :=
  ⟨by
    rintro _ ⟨x, rfl⟩ α
    refine ⟨α x, ?_⟩
    ext y
    simp [MulAut.mul_apply]⟩

/-- `Out(G) = Aut(G)/Inn(G)`. -/
abbrev Out (G : Type u) [Group G] : Type u := MulAut G ⧸ (MulAut.conj (G := G)).range

/-- `Aut(G,S) = {β ∈ Aut(G) | β(S) = S}`. -/
def autGS : Subgroup (MulAut G) where
  carrier := {β | S.map β.toMonoidHom = S}
  one_mem' := map_refl S
  mul_mem' := by
    intro a b ha hb
    show S.map (b.trans a).toMonoidHom = S
    rw [← map_map_equiv, hb, ha]
  inv_mem' := by
    intro a ha
    exact map_symm_map a ha

variable {S}

lemma isEquivalence_mapFunctor (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    (mapFunctor p β hβ).IsEquivalence :=
  (Cat.equivOfIso (mapIso p β hβ)).isEquivalence_functor

lemma isIsotypical_mapFunctor (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    IsIsotypical p S (mapFunctor p β hβ) := by
  intro P
  ext m
  constructor
  · rintro ⟨_, ⟨x, hx, hxP, rfl⟩, rfl⟩
    exact ⟨β x, mem_transporter_map β hx, mem_map_of_mem _ hxP, rfl⟩
  · rintro ⟨y, hy, ⟨x, hxP, rfl⟩, rfl⟩
    exact ⟨mk p x (mem_transporter_self hxP), ⟨x, _, hxP, rfl⟩, rfl⟩

lemma mapFunctor_mul (β β' : MulAut G) (hβ : S.map β.toMonoidHom = S)
    (hβ' : S.map β'.toMonoidHom = S) (h : S.map (β * β').toMonoidHom = S) :
    mapFunctor p (β * β') h = mapFunctor p β' hβ' ⋙ mapFunctor p β hβ := by
  rw [mapFunctor_comp]; rfl

/-- For `n ∈ N_G(S)`, conjugation by `n` is naturally isomorphic to the identity of `L^c_S(G)`,
via `P ↦ [n] : P → nPn⁻¹`. -/
def conjNatIso (n : G) (hn : S.map (MulAut.conj n).toMonoidHom = S) :
    𝟭 (Obj p S) ≅ mapFunctor p (MulAut.conj n) hn :=
  NatIso.ofComponents
    (fun P => by
      refine ⟨mk p n ?_, mk p n⁻¹ ?_, ?_, ?_⟩
      · intro x hx; exact ⟨x, hx, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩; simpa [mul_assoc] using hx
      · exact mk_congr p (inv_mul_cancel n) _ _
      · exact mk_congr p (mul_inv_cancel n) _ _)
    (by
      rintro P Q ⟨⟨g, hg⟩⟩
      exact mk_congr p (by simp [mul_assoc]) _ _)

/-- The class in `Out_typ(L)` of `P ↦ β(P)`, `[g] ↦ [β(g)]`, for `β ∈ Aut(G,S)`. -/
def kappaElt (β : MulAut G) (hβ : S.map β.toMonoidHom = S) : OutTyp p S :=
  (natIsoCon p S).mk' ⟨(mapFunctor p β hβ).toCatHom,
    isEquivalence_mapFunctor p β hβ, isIsotypical_mapFunctor p β hβ⟩

lemma kappaElt_mul (β β' : MulAut G) (hβ : S.map β.toMonoidHom = S)
    (hβ' : S.map β'.toMonoidHom = S) (h : S.map (β * β').toMonoidHom = S) :
    kappaElt p (β * β') h = kappaElt p β hβ * kappaElt p β' hβ' := by
  rw [kappaElt, kappaElt, kappaElt, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Cat.ext
  exact mapFunctor_mul p β β' hβ hβ' h

lemma kappaElt_congr {β β' : MulAut G} (e : β = β') (hβ : S.map β.toMonoidHom = S)
    (hβ' : S.map β'.toMonoidHom = S) : kappaElt p β hβ = kappaElt p β' hβ' := by
  subst e; rfl

lemma kappaElt_one (h : S.map (1 : MulAut G).toMonoidHom = S) : kappaElt p 1 h = 1 := by
  rw [kappaElt, ← map_one ((natIsoCon p S).mk')]
  congr 1
  apply Subtype.ext
  apply Cat.ext
  exact mapFunctor_refl p h

lemma kappaElt_conj_mul (n : G) (hn : S.map (MulAut.conj n).toMonoidHom = S) (β : MulAut G)
    (hβ : S.map β.toMonoidHom = S) (h : S.map (MulAut.conj n * β).toMonoidHom = S) :
    kappaElt p (MulAut.conj n * β) h = kappaElt p β hβ := by
  rw [kappaElt_mul p _ _ hn hβ h]
  have : kappaElt p (MulAut.conj n) hn = 1 := by
    rw [← kappaElt_one p (map_refl S)]
    apply (natIsoCon p S).eq.2
    exact ⟨(conjNatIso p n hn).symm ≪≫ eqToIso (mapFunctor_refl p (map_refl S)).symm⟩
  rw [this, one_mul]

end AndersenOliverVentura.Tame
