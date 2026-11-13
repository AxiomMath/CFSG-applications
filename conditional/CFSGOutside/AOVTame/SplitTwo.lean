import CFSGOutside.AOVTame.Decomp
import CFSGOutside.AOVTame.Kappa

/-!
# AOV tameness: splitting `κ_{A × B}` when every automorphism preserves both factors

If every `α ∈ Aut_typ^I(L(A × B))` preserves `S_A × 1` and `1 × S_B`, then splittings of `κ_A` and
`κ_B` give a splitting of `κ_{A × B}` (AOV, proof of Theorem 3.6, the part on `Out⁰_typ`).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory

universe u

section Class
variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}

variable (p) in
/-- `P ↦ β(P)`, `[g] ↦ [β(g)]`, as an element of `Aut(L)`. -/
def mapAut (β : MulAut G) (hβ : S.map β.toMonoidHom = S) : LAut p S := mapIso p β hβ

variable (p) in
lemma mapAut_mem (β : MulAut G) (hβ : S.map β.toMonoidHom = S) : mapAut p β hβ ∈ autTypI p S :=
  mapIso_mem p β hβ

lemma mapAut_fn (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    (mapAut p β hβ).fn = mapFunctor p β hβ := rfl

lemma isEquivalence_laut (α : LAut p S) : α.fn.IsEquivalence :=
  (Cat.equivOfIso α).isEquivalence_functor

/-- The class of `α ∈ Aut_typ^I` in `Out_typ`. -/
def autClass {α : LAut p S} (hα : α ∈ autTypI p S) : OutTyp p S :=
  (natIsoCon p S).mk' ⟨α.hom, isEquivalence_laut α, hα.1⟩

lemma autClass_mul {α α' : LAut p S} (hα : α ∈ autTypI p S) (hα' : α' ∈ autTypI p S) :
    autClass (mul_mem hα hα') = autClass hα * autClass hα' := by
  rw [autClass, autClass, autClass, ← map_mul]
  rfl

lemma autClass_eq_of_iso {α α' : LAut p S} (hα : α ∈ autTypI p S) (hα' : α' ∈ autTypI p S)
    (ω : α.fn ≅ α'.fn) : autClass hα = autClass hα' :=
  (natIsoCon p S).eq.2 ⟨ω⟩

lemma autClass_congr {α α' : LAut p S} (h : α = α') (hα : α ∈ autTypI p S)
    (hα' : α' ∈ autTypI p S) : autClass hα = autClass hα' := by subst h; rfl

lemma autClass_mapIso_conj (n : G) (hn : S.map (MulAut.conj n).toMonoidHom = S) :
    autClass (mapAut_mem p (MulAut.conj n) hn) = 1 := by
  show (natIsoCon p S).mk' _ = 1
  rw [← map_one ((natIsoCon p S).mk')]
  apply (natIsoCon p S).eq.2
  exact ⟨(conjNatIso p n hn).symm⟩

lemma autClass_eq_kappaElt (β : MulAut G) (hβ : S.map β.toMonoidHom = S) :
    autClass (mapAut_mem p β hβ) = kappaElt p β hβ := rfl

end Class

section Beta
variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {T : Sylow p G}

lemma betaFun_mapIso (γ : MulAut G) (hγ : (T : Subgroup G).map γ.toMonoidHom = T)
    (x : (T : Subgroup G)) : (betaFun (mapAut_mem p γ hγ) x : G) = γ x := by
  obtain ⟨hb, e⟩ := map_mk_delta (mapAut_mem p γ hγ) (topObj T) (x := (x : G)) x.2
  have e' : (mapAut p γ hγ).fn.map
      (show topObj T ⟶ topObj T from mk p x (mem_transporter_self x.2)) =
      mk p (γ x) (mem_transporter_map _ (mem_transporter_self x.2)) := rfl
  rw [e'] at e
  have h1 := (mk_eq_mk p).1 e
  have hxS : (γ x : G) ∈ ((mapAut p γ hγ).fn.obj (topObj T)).val :=
    ⟨x, x.2, rfl⟩
  have h2 := eq_one_of_mem_opCent T ((mapAut p γ hγ).fn.obj (topObj T)).2 h1
    (mul_mem (inv_mem (((mapAut p γ hγ).fn.obj (topObj T)).2.1 hxS))
      (betaFun _ x).2)
  exact (inv_mul_eq_one.1 h2).symm

end Beta

section Prod
variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

lemma prodCongr_mem {γA : MulAut A} {γB : MulAut B}
    (hA : (SA : Subgroup A).map γA.toMonoidHom = SA) (hB : (SB : Subgroup B).map γB.toMonoidHom = SB) :
    ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map
      (MulEquiv.prodCongr γA γB).toMonoidHom = (prodSylow SA SB : Sylow p (A × B)) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, e⟩
    change (γA x, γB y) = (a, b) at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    refine ⟨?_, ?_⟩
    · rw [← hA]; exact mem_map_of_mem _ hx
    · rw [← hB]; exact mem_map_of_mem _ hy
  · rintro ⟨ha, hb⟩
    rw [← hA] at ha; rw [← hB] at hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

variable {γA : MulAut A} {γB : MulAut B} (hA : (SA : Subgroup A).map γA.toMonoidHom = SA)
  (hB : (SB : Subgroup B).map γB.toMonoidHom = SB)

lemma presFactors_mapIso :
    PresFactors (mapAut_mem p (MulEquiv.prodCongr γA γB) (prodCongr_mem hA hB)) := by
  constructor
  · intro a ha
    rw [betaFun_mapIso]; exact map_one γB
  · intro b hb
    rw [betaFun_mapIso]; exact map_one γA

lemma fnA_mapIso :
    fnA SB (α := mapAut p (MulEquiv.prodCongr γA γB) (prodCongr_mem hA hB)) = mapFunctor p γA hA := by
  have hobj : ∀ P : Obj p (SA : Subgroup A),
      (fnA SB (α := mapAut p (MulEquiv.prodCongr γA γB) (prodCongr_mem hA hB))).obj P =
      (mapFunctor p γA hA).obj P := by
    intro P
    apply Obj.ext
    change ((P.val.prod (SB : Subgroup B)).map (MulEquiv.prodCongr γA γB).toMonoidHom).map
      (MonoidHom.fst A B) = P.val.map γA.toMonoidHom
    rw [map_map]
    ext a
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨(x, 1), ⟨hx, one_mem _⟩, rfl⟩
  refine Functor.hext hobj ?_
  rintro P Q ⟨⟨g, hg⟩⟩
  exact mk_heq p (congrArg Obj.val (hobj P)) (congrArg Obj.val (hobj Q)) rfl _ _

lemma phiFunctor_mapIso :
    phiFunctor SB (mapAut_mem p γA hA) =
      mapFunctor p (MulEquiv.prodCongr γA (MulEquiv.refl B)) (prodCongr_mem hA (map_refl _)) := by
  have hobj : ∀ P : Obj p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)),
      (phiObj SB (mapAut_mem p γA hA) P).val =
        P.val.map (MulEquiv.prodCongr γA (MulEquiv.refl B)).toMonoidHom := by
    intro P
    ext z
    change z ∈ bmap _ P.val ↔ _
    rw [mem_bmap_bX_iff]
    constructor
    · rintro ⟨x, hx, h1, h2, rfl⟩
      refine ⟨x, hx, Prod.ext ?_ rfl⟩
      rw [betaFun_mapIso]; rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, (P.2.1 hx).1, (P.2.1 hx).2, Prod.ext ?_ rfl⟩
      rw [betaFun_mapIso]; rfl
  apply Functor.hext (fun P => Obj.ext (hobj P))
  rintro P Q ⟨⟨g, hg⟩⟩
  have e : (mapAut p γA hA).fn.map
      (show proj₁ P ⟶ proj₁ Q from mk p g.1 (mem_transporter_fst hg)) =
      mk p (γA g.1) (mem_transporter_map _ (mem_transporter_fst hg)) := rfl
  change HEq (phiMor SB (mapAut_mem p γA hA) (mk p g hg)) _
  rw [phiMor_mk (mapAut_mem p γA hA) hg _ e]
  exact mk_heq p (hobj P) (hobj Q) rfl _ _

lemma phiBAut_mapIso_fn :
    (phiBAut (SA := SA) (mapAut_mem p γB hB)).fn =
      mapFunctor p (MulEquiv.prodCongr (MulEquiv.refl A) γB) (prodCongr_mem (map_refl _) hB) := by
  unfold phiBAut
  rw [conjIso_fn, phiAut_fn, phiFunctor_mapIso, mapFunctor_comp, mapFunctor_comp]
  exact mapFunctor_congr p (by ext ⟨a, b⟩ <;> rfl) _ _

end Prod

section Classes
variable {A B : Type u} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
  {SA : Sylow p A} {SB : Sylow p B}

lemma lautA_mul {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') :
    lautA SB (mul_mem hα hα') (presFactors_mul hα hf hα' hf') = lautA SB hα hf * lautA SB hα' hf' :=
  LAut.ext_fn p _ (fnA_mul hα' hf')

lemma classA_mul {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') :
    autClass (lautA_mem (mul_mem hα hα') (presFactors_mul hα hf hα' hf')) =
      autClass (lautA_mem hα hf) * autClass (lautA_mem hα' hf') := by
  rw [← autClass_mul]
  exact autClass_congr (lautA_mul hα hf hα' hf') _ _

lemma conj_fst_mem {n : A × B}
    (hn : ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map (MulAut.conj n).toMonoidHom =
      (prodSylow SA SB : Sylow p (A × B))) :
    (SA : Subgroup A).map (MulAut.conj n.1).toMonoidHom = SA := by
  have ht : n.1 ∈ transporter (SA : Subgroup A) (SA : Subgroup A) := by
    intro a ha
    have : n * (a, 1) * n⁻¹ ∈ ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) := by
      rw [← hn]; exact ⟨(a, 1), ⟨ha, one_mem _⟩, rfl⟩
    exact this.1
  exact transporter_self_conj ht

lemma conj_snd_mem {n : A × B}
    (hn : ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)).map (MulAut.conj n).toMonoidHom =
      (prodSylow SA SB : Sylow p (A × B))) :
    (SB : Subgroup B).map (MulAut.conj n.2).toMonoidHom = SB := by
  have ht : n.2 ∈ transporter (SB : Subgroup B) (SB : Subgroup B) := by
    intro b hb
    have : n * (1, b) * n⁻¹ ∈ ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)) := by
      rw [← hn]; exact ⟨(1, b), ⟨one_mem _, hb⟩, rfl⟩
    exact this.2
  exact transporter_self_conj ht

lemma classA_eq_of_iso {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') (ω : α.fn ≅ α'.fn) :
    autClass (lautA_mem hα hf) = autClass (lautA_mem hα' hf') := by
  obtain ⟨n, hn, e⟩ := eq_conj_of_iso hα hα' ω
  have h1 := conj_fst_mem hn
  have h2 := conj_snd_mem hn
  set c := mapAut p (MulEquiv.prodCongr (MulAut.conj n.1) (MulAut.conj n.2)) (prodCongr_mem h1 h2)
  have hc := mapAut_mem p (MulEquiv.prodCongr (MulAut.conj n.1) (MulAut.conj n.2)) (prodCongr_mem h1 h2)
  have hcf := presFactors_mapIso (SA := SA) (SB := SB) h1 h2
  have he : α' = c * α := by
    apply LAut.ext_fn
    rw [LAut.fn_mul, e, mapAut_fn]
    congr 1
  have h3 : autClass (lautA_mem hα' hf') = autClass (lautA_mem (mul_mem hc hα) (presFactors_mul hc hcf hα hf)) := by
    subst he; rfl
  rw [h3, classA_mul hc hcf hα hf]
  have h4 : autClass (lautA_mem hc hcf) = 1 := by
    rw [← autClass_mapIso_conj (p := p) (S := (SA : Subgroup A)) n.1 h1]
    apply autClass_congr
    apply LAut.ext_fn
    rw [lautA_fn]
    exact fnA_mapIso h1 h2
  rw [h4, one_mul]

lemma classB_mul {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') :
    autClass (lautB_mem (mul_mem hα hα') (presFactors_mul hα hf hα' hf')) =
      autClass (lautB_mem hα hf) * autClass (lautB_mem hα' hf') := by
  have hs : swapAut (α * α') = swapAut α * swapAut α' := conjIso_mul _ _ α α'
  have h1 : autClass (lautB_mem (mul_mem hα hα') (presFactors_mul hα hf hα' hf')) =
      autClass (lautA_mem (mul_mem (swapAut_mem hα) (swapAut_mem hα'))
        (presFactors_mul (swapAut_mem hα) (presFactors_swap hα hf) (swapAut_mem hα')
          (presFactors_swap hα' hf'))) := by
    apply autClass_congr
    apply LAut.ext_fn
    exact fnA_congr hs
  rw [h1, classA_mul]
  rfl

lemma classB_eq_of_iso {α α' : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα)
    (hα' : α' ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf' : PresFactors hα') (ω : α.fn ≅ α'.fn) :
    autClass (lautB_mem hα hf) = autClass (lautB_mem hα' hf') := by
  have ω' : (swapAut α).fn ≅ (swapAut α').fn := by
    unfold swapAut
    rw [conjIso_fn, conjIso_fn]
    exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ω _)
  exact classA_eq_of_iso (swapAut_mem hα) (presFactors_swap hα hf) (swapAut_mem hα')
    (presFactors_swap hα' hf') ω'

lemma autClass_decomp {α : LAut p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B))}
    (hα : α ∈ autTypI p ((prodSylow SA SB : Sylow p (A × B)) : Subgroup (A × B)))
    (hf : PresFactors hα) :
    autClass hα = autClass (phiAut_mem (SB := SB) (lautA_mem hα hf)) *
      autClass (phiBAut_mem (SA := SA) (lautB_mem hα hf)) := by
  rw [← autClass_mul]
  apply autClass_congr
  apply LAut.ext_fn
  rw [LAut.fn_mul, phiAut_fn]
  exact decomp hα hf

lemma autClass_phiAut_eq {γ γ' : LAut p (SA : Subgroup A)} (hγ : γ ∈ autTypI p (SA : Subgroup A))
    (hγ' : γ' ∈ autTypI p (SA : Subgroup A)) (ω : γ.fn ≅ γ'.fn) :
    autClass (phiAut_mem (SB := SB) hγ) = autClass (phiAut_mem (SB := SB) hγ') :=
  phiClass_eq_of_iso hγ hγ' ω

lemma autClass_phiBAut_eq {γ γ' : LAut p (SB : Subgroup B)} (hγ : γ ∈ autTypI p (SB : Subgroup B))
    (hγ' : γ' ∈ autTypI p (SB : Subgroup B)) (ω : γ.fn ≅ γ'.fn) :
    autClass (phiBAut_mem (SA := SA) hγ) = autClass (phiBAut_mem (SA := SA) hγ') := by
  have h := phiClass_eq_of_iso (SB := SA) hγ hγ' ω
  obtain ⟨ν⟩ := (natIsoCon p _).eq.1 h
  apply autClass_eq_of_iso
  unfold phiBAut
  rw [conjIso_fn, conjIso_fn]
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ν _)

end Classes

section OutProd
variable {A B : Type u} [Group A] [Group B]

/-- `(γ_A, γ_B) ↦ γ_A × γ_B`. -/
def prodAut : MulAut A × MulAut B →* MulAut (A × B) where
  toFun x := MulEquiv.prodCongr x.1 x.2
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

/-- `Out(A) → Out(A × B)`. -/
def outInl : Out A →* Out (A × B) :=
  QuotientGroup.map _ _ ((prodAut (A := A) (B := B)).comp (MonoidHom.inl _ _)) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a, 1), by ext <;> simp [prodAut] <;> rfl⟩)

/-- `Out(B) → Out(A × B)`. -/
def outInr : Out B →* Out (A × B) :=
  QuotientGroup.map _ _ ((prodAut (A := A) (B := B)).comp (MonoidHom.inr _ _)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨(1, b), by ext <;> simp [prodAut] <;> rfl⟩)

/-- `Out(A) × Out(B) → Out(A × B)`. -/
def outProd : Out A × Out B →* Out (A × B) :=
  (outInl (A := A) (B := B)).noncommCoprod outInr (by
    intro x y
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective y
    change Commute (QuotientGroup.mk _ : Out (A × B)) (QuotientGroup.mk _)
    rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1)

lemma outProd_mk (γ : MulAut A) (δ : MulAut B) :
    outProd ((QuotientGroup.mk γ : Out A), (QuotientGroup.mk δ : Out B)) =
      (QuotientGroup.mk (MulEquiv.prodCongr γ δ) : Out (A × B)) := by
  change (QuotientGroup.mk _ : Out (A × B)) * QuotientGroup.mk _ = _
  rw [← QuotientGroup.mk_mul]
  congr 1

end OutProd

end AndersenOliverVentura.Tame
