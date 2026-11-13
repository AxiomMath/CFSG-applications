import CFSGOutside.AOVTame.Setup
import CFSGOutside.AOVTame.SplitAux
import CFSGOutside.AOVTame.AutKer
import CFSGOutside.AOVTame.KappaCompat

/-!
# AOV tameness: the automorphism `γ` of `G` lifting `α × Id`

In the setting of `Setup`, let `α₁ ∈ Aut_typ^I(L^c_{S₁}(G₁))` and suppose that the transport
`Ψ` of `α₁ × Id` to `L^c_T(G)` is naturally isomorphic to `κ`-image of some `γ₀ ∈ Aut(G, T)`.
Then some `γ ∈ γ₀ Inn(G)` satisfies `γ(P) = Ψ(P)`, `γ[g] = Ψ[g]` exactly; such a `γ` acts on
`E(S₁)` as `α₁` does, fixes `E(S₂)` pointwise, hence normalizes `G₂`, and induces on `G/G₂` an
automorphism whose `κ`-class is the transport of `[α₁]` along `ν : G₁ → G/G₂`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S S₁ S₂ : Type} [Group S] [Group S₁] [Group S₂] [Finite S]
  {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} {d : ProdData S S₁ S₂}
  {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {E : S →* G}

/-- Transport of `F (mk g)` along equalities of objects. -/
lemma map_mk_transport {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {SK : Subgroup K}
    (Φ : Obj p SK ⥤ Obj p SK) {P P' Q Q' : Obj p SK} (hP : P = P') (hQ : Q = Q') {g : K}
    (hg : g ∈ transporter P.val Q.val) (hg' : g ∈ transporter P'.val Q'.val) {k : K}
    (hk : k ∈ transporter (Φ.obj P).val (Φ.obj Q).val)
    (hk' : k ∈ transporter (Φ.obj P').val (Φ.obj Q').val)
    (e : Φ.map (show P ⟶ Q from mk p g hg) = mk p k hk) :
    Φ.map (show P' ⟶ Q' from mk p g hg') = mk p k hk' := by
  subst hP hQ; exact e

lemma map_mul_toMonoidHom {K : Type*} [Group K] (β β' : MulAut K) (P : Subgroup K) :
    P.map (β * β').toMonoidHom = (P.map β'.toMonoidHom).map β.toMonoidHom := by
  rw [map_map]; rfl

section
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E)
include h

/-- The product linking system's top object. -/
abbrev Hyp.Lp := Obj 2 ((prodSylow h.SA h.SB : Sylow 2 (G₁ d E × G₂ d E)) : Subgroup (G₁ d E × G₂ d E))

/-- Step 1: adjust `γ₀` by an inner automorphism so that `γ` realizes `Ψ` exactly. -/
lemma Hyp.exists_good {α₁ : LAut 2 (h.SA : Subgroup (G₁ d E))}
    (hα₁ : α₁ ∈ autTypI 2 (h.SA : Subgroup (G₁ d E))) (γ₀ : MulAut G)
    (hγ₀ : (T : Subgroup G).map γ₀.toMonoidHom = T)
    (ω : Nonempty (mapFunctor 2 γ₀ hγ₀ ≅ (h.fusionHom_μ.conjAut (phiAut h.SB hα₁)).fn)) :
    ∃ (γ : MulAut G) (hγ : (T : Subgroup G).map γ.toMonoidHom = T),
      (QuotientGroup.mk γ : Out G) = QuotientGroup.mk γ₀ ∧
      h.fusionHom_μ.fwd ⋙ mapFunctor 2 γ hγ = phiFunctor h.SB hα₁ ⋙ h.fusionHom_μ.fwd := by
  obtain ⟨n, hn, e⟩ := eq_conj_of_iso (mapIso_mem 2 γ₀ hγ₀)
    (h.fusionHom_μ.conjAut_mem (phiAut_mem hα₁)) ω.some
  have hγ : (T : Subgroup G).map (MulAut.conj n * γ₀).toMonoidHom = T := by
    rw [map_mul_toMonoidHom, hγ₀, hn]
  refine ⟨MulAut.conj n * γ₀, hγ, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨n, rfl⟩), one_mul]
  · rw [mapFunctor_mul 2 _ _ hn hγ₀ hγ]
    change h.fusionHom_μ.fwd ⋙ (mapIso 2 γ₀ hγ₀).hom.toFunctor ⋙ mapFunctor 2 (MulAut.conj n) hn = _
    rw [← e, h.fusionHom_μ.conjAut_fn, ← Functor.assoc, h.fusionHom_μ.fwd_bwd]
    rfl

end

section Good
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E) {α₁ : LAut 2 (h.SA : Subgroup (G₁ d E))}
  (hα₁ : α₁ ∈ autTypI 2 (h.SA : Subgroup (G₁ d E))) {γ : MulAut G}
  (hγ : (T : Subgroup G).map γ.toMonoidHom = T)
  (hfun : h.fusionHom_μ.fwd ⋙ mapFunctor 2 γ hγ = phiFunctor h.SB hα₁ ⋙ h.fusionHom_μ.fwd)
include h hfun

/-- Step 2: the functor identity, on a morphism `[g] : X → Y` of `L(G₁ × G₂)`. -/
lemma Hyp.key_rel {X Y : h.Lp} {g : G₁ d E × G₂ d E} (hg : g ∈ transporter X.val Y.val) {k : G₁ d E}
    (hk : k ∈ transporter (α₁.fn.obj (proj₁ X)).val (α₁.fn.obj (proj₁ Y)).val)
    (e : α₁.fn.map (show proj₁ X ⟶ proj₁ Y from Tame.mk 2 g.1 (mem_transporter_fst hg)) = Tame.mk 2 k hk) :
    (γ (h.μ g))⁻¹ * h.μ (k, g.2) ∈ opCent 2 ((X.val.map h.μ).map γ.toMonoidHom) := by
  have hh := Functor.hcongr_hom hfun (show X ⟶ Y from Tame.mk 2 g hg)
  change HEq (Mor.map 2 γ (h.fusionHom_μ.fwdMor (Tame.mk 2 g hg)))
    (h.fusionHom_μ.fwdMor (phiMor h.SB hα₁ (show X ⟶ Y from Tame.mk 2 g hg))) at hh
  rw [phiMor_mk hα₁ hg hk e, FusionHom.fwdMor_mk, FusionHom.fwdMor_mk, Mor.map_mk] at hh
  exact mk_rel_of_heq (congrArg Obj.val (Functor.congr_obj hfun X))
    (congrArg Obj.val (Functor.congr_obj hfun Y)) hh

omit hfun in
lemma Hyp.proj₁_top : proj₁ (topObj (prodSylow h.SA h.SB)) = topObj h.SA := by
  apply Obj.ext
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx.1
  · intro hy; exact ⟨(y, 1), ⟨hy, one_mem _⟩, rfl⟩

/-- Step 3: `γ(a b) = α₁(a) b` for `a ∈ S_A`, `b ∈ S_B`. -/
lemma Hyp.gamma_mu {a : G₁ d E} (ha : a ∈ (h.SA : Subgroup (G₁ d E))) {b : G₂ d E}
    (hb : b ∈ (h.SB : Subgroup (G₂ d E))) :
    γ (h.μ (a, b)) = h.μ ((betaFun hα₁ ⟨a, ha⟩ : G₁ d E), b) := by
  have hab : (a, b) ∈ ((prodSylow h.SA h.SB : Sylow 2 _) : Subgroup (G₁ d E × G₂ d E)) := ⟨ha, hb⟩
  have hβ := (betaFun hα₁ ⟨a, ha⟩).2
  have e := map_mk_transport α₁.fn h.proj₁_top.symm h.proj₁_top.symm (mem_transporter_self ha)
    (mem_transporter_fst (mem_transporter_self hab))
    (mem_transporter_self ((val_obj_top hα₁).symm ▸ hβ))
    (by rw [h.proj₁_top]; exact mem_transporter_self ((val_obj_top hα₁).symm ▸ hβ))
    (map_mk_top hα₁ ⟨a, ha⟩)
  have hc := h.key_rel hα₁ hγ hfun
    (mem_transporter_self (show (a, b) ∈ (topObj (prodSylow h.SA h.SB)).val from hab)) _ e
  have hR := ((h.fusionHom_μ.fwd ⋙ mapFunctor 2 γ hγ).obj (topObj (prodSylow h.SA h.SB))).2
  have hT : ∀ z ∈ ((prodSylow h.SA h.SB : Sylow 2 _) : Subgroup (G₁ d E × G₂ d E)),
      h.μ z ∈ (T : Subgroup G) := fun z hz => h.fusionHom_μ.map_eq ▸ mem_map_of_mem _ hz
  have hγT : ∀ t ∈ (T : Subgroup G), γ t ∈ (T : Subgroup G) := fun t ht =>
    hγ ▸ mem_map_of_mem γ.toMonoidHom ht
  have h1 := eq_one_of_mem_opCent T hR hc (mul_mem (inv_mem (hγT _ (hT _ hab)))
    (hT _ ⟨hβ, hb⟩))
  exact (inv_mul_eq_one.1 h1)

lemma Hyp.gamma_fix (b : S₂) : γ (E (d.ι₂ b)) = E (d.ι₂ b) := by
  have h1 := h.gamma_mu hα₁ hγ hfun (one_mem _) (⟨b, rfl⟩ : e₂ d E b ∈ (h.SB : Subgroup (G₂ d E)))
  have h2 : betaFun hα₁ ⟨1, one_mem _⟩ = 1 := by
    rw [← beta_apply hα₁]; exact map_one _
  rw [h2] at h1
  simpa using h1

lemma Hyp.gamma_G₂ : (G₂ d E).map γ.toMonoidHom = G₂ d E := by
  rw [G₂, map_normalClosure _ _ γ.surjective]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, (h.gamma_fix hα₁ hγ hfun b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨E (d.ι₂ b), ⟨b, rfl⟩, h.gamma_fix hα₁ hγ hfun b⟩

end Good

/-- `γ` induces an automorphism `γ̄` of `G/G₂`. -/
def quot₂ (γ : MulAut G) (hG : (G₂ d E).map γ.toMonoidHom = G₂ d E) : MulAut (H d E) :=
  QuotientGroup.congr _ _ γ hG

@[simp] lemma quot₂_mk (γ : MulAut G) (hG : (G₂ d E).map γ.toMonoidHom = G₂ d E) (x : G) :
    quot₂ γ hG (QuotientGroup.mk x : H d E) = QuotientGroup.mk (γ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

lemma quot₂_Tbar (γ : MulAut G) (hG : (G₂ d E).map γ.toMonoidHom = G₂ d E)
    (hγ : (T : Subgroup G).map γ.toMonoidHom = T) :
    (Tbar d E T : Subgroup (H d E)).map (quot₂ γ hG).toMonoidHom = Tbar d E T := by
  rw [Tbar, Sylow.coe_mapSurjective]
  conv_rhs => rw [← hγ]
  rw [map_map, map_map]
  congr 1

section Good2
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E) {α₁ : LAut 2 (h.SA : Subgroup (G₁ d E))}
  (hα₁ : α₁ ∈ autTypI 2 (h.SA : Subgroup (G₁ d E))) {γ : MulAut G}
  (hγ : (T : Subgroup G).map γ.toMonoidHom = T)
  (hfun : h.fusionHom_μ.fwd ⋙ mapFunctor 2 γ hγ = phiFunctor h.SB hα₁ ⋙ h.fusionHom_μ.fwd)
include h hfun

lemma Hyp.gamma_SA (x : (h.SA : Subgroup (G₁ d E))) :
    γ ((x : G₁ d E) : G) = ((betaFun hα₁ x : G₁ d E) : G) := by
  have := h.gamma_mu hα₁ hγ hfun x.2 (one_mem _)
  simp only [Hyp.μ_apply, OneMemClass.coe_one, mul_one] at this
  exact this

lemma Hyp.obj_eq (P : Obj 2 (h.SA : Subgroup (G₁ d E))) :
    (α₁.fn.obj P).val.map (ν d E) =
      (P.val.map (ν d E)).map (quot₂ γ (h.gamma_G₂ hα₁ hγ hfun)).toMonoidHom := by
  rw [obj_val_eq hα₁ P]
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨ν d E x, ⟨x, hx, rfl⟩, ?_⟩
    change quot₂ γ _ (QuotientGroup.mk ((x : G₁ d E) : G)) = QuotientGroup.mk _
    rw [quot₂_mk, h.gamma_SA hα₁ hγ hfun x]
    rfl
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    let x : (h.SA : Subgroup (G₁ d E)) := ⟨y, P.2.1 hy⟩
    refine ⟨_, ⟨_, ⟨x, (show (x : G₁ d E) ∈ P.val from hy), rfl⟩, rfl⟩, ?_⟩
    change QuotientGroup.mk _ = quot₂ γ _ (QuotientGroup.mk ((x : G₁ d E) : G))
    rw [quot₂_mk, h.gamma_SA hα₁ hγ hfun x]
    rfl

/-- The object `P × S_B` of `L(G₁ × G₂)`. -/
def Hyp.prodObj (P : Obj 2 (h.SA : Subgroup (G₁ d E))) : h.Lp :=
  ⟨P.val.prod (h.SB : Subgroup (G₂ d E)), isCentric_prod P.2 (isCentric_self h.SB)⟩

omit hfun in
lemma Hyp.proj₁_prodObj (P : Obj 2 (h.SA : Subgroup (G₁ d E))) : proj₁ (h.prodObj P) = P := by
  apply Obj.ext
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx.1
  · intro hy; exact ⟨(y, 1), ⟨hy, one_mem _⟩, rfl⟩

lemma Hyp.prodObj_eq (P : Obj 2 (h.SA : Subgroup (G₁ d E))) :
    (((h.prodObj P).val.map h.μ).map γ.toMonoidHom).map (QuotientGroup.mk' (G₂ d E)) =
      (α₁.fn.obj P).val.map (ν d E) := by
  rw [obj_val_eq hα₁ P]
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨⟨x, b⟩, ⟨hx, hb⟩, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, mem_bmap (⟨x, P.2.1 hx⟩ : (h.SA : Subgroup (G₁ d E))) hx, ?_⟩
    change QuotientGroup.mk _ = QuotientGroup.mk (γ (h.μ (x, b)))
    rw [h.gamma_mu hα₁ hγ hfun (P.2.1 hx) hb, Hyp.μ_apply]
    apply (QuotientGroup.eq).2
    rw [show ((G₁ d E).subtype (beta hα₁ ⟨x, P.2.1 hx⟩) : G) =
      ((betaFun hα₁ ⟨x, P.2.1 hx⟩ : G₁ d E) : G) from rfl, inv_mul_cancel_left]
    exact b.2
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨((x : G₁ d E), 1), ⟨hx, one_mem _⟩, rfl⟩, rfl⟩, ?_⟩
    change QuotientGroup.mk (γ (h.μ ((x : G₁ d E), 1))) = QuotientGroup.mk _
    rw [h.gamma_mu hα₁ hγ hfun x.2 (one_mem _), Hyp.μ_apply]
    simp
    rfl

/-- Step 6: `α₁` and `γ̄` correspond under `ν`. -/
lemma Hyp.ffun : α₁.fn ⋙ h.fusionHom_ν.fwd =
    h.fusionHom_ν.fwd ⋙ mapFunctor 2 (quot₂ γ (h.gamma_G₂ hα₁ hγ hfun))
      (quot₂_Tbar γ (h.gamma_G₂ hα₁ hγ hfun) hγ) := by
  have hobj : ∀ P, (α₁.fn ⋙ h.fusionHom_ν.fwd).obj P = (h.fusionHom_ν.fwd ⋙ mapFunctor 2
      (quot₂ γ (h.gamma_G₂ hα₁ hγ hfun)) (quot₂_Tbar γ (h.gamma_G₂ hα₁ hγ hfun) hγ)).obj P :=
    fun P => Obj.ext (h.obj_eq hα₁ hγ hfun P)
  apply Functor.hext hobj
  rintro P Q ⟨⟨g, hg⟩⟩
  obtain ⟨⟨g', hg'⟩, eg'⟩ := Quotient.exists_rep (α₁.fn.map (show P ⟶ Q from Tame.mk 2 g hg))
  change HEq (h.fusionHom_ν.fwdMor (α₁.fn.map (Tame.mk 2 g hg)))
    (Mor.map 2 (quot₂ γ _) (h.fusionHom_ν.fwdMor (Tame.mk 2 g hg)))
  rw [← eg']
  change HEq (h.fusionHom_ν.fwdMor (Tame.mk 2 g' hg')) _
  rw [FusionHom.fwdMor_mk, FusionHom.fwdMor_mk, Mor.map_mk]
  apply mk_heq_of_mem 2 (congrArg Obj.val (hobj P)) (congrArg Obj.val (hobj Q))
  -- the relation from `L(G₁ × G₂)`, pushed to `G/G₂`
  have hg1 : ((g, 1) : G₁ d E × G₂ d E) ∈ transporter (h.prodObj P).val (h.prodObj Q).val := by
    rintro ⟨x, b⟩ ⟨hx, hb⟩
    refine ⟨hg x hx, ?_⟩
    simpa using hb
  have e := map_mk_transport α₁.fn (h.proj₁_prodObj P).symm (h.proj₁_prodObj Q).symm hg
    (mem_transporter_fst hg1) hg'
    (by rw [h.proj₁_prodObj, h.proj₁_prodObj]; exact hg') (show _ = Tame.mk 2 g' hg' from eg'.symm)
  have hc := h.key_rel hα₁ hγ hfun hg1 _ e
  have hc' := map_opCent_le_hom (p := 2) (QuotientGroup.mk' (G₂ d E)) _ ⟨_, inv_mem hc, rfl⟩
  rw [h.prodObj_eq hα₁ hγ hfun P] at hc'
  convert hc' using 1
  · rfl
  rw [map_inv, map_mul, map_inv, Hyp.μ_apply, Hyp.μ_apply]
  simp only [OneMemClass.coe_one, mul_one, mul_inv_rev, inv_inv, QuotientGroup.mk'_apply]
  change (QuotientGroup.mk ((g' : G₁ d E) : G) : H d E)⁻¹ *
      quot₂ γ _ (QuotientGroup.mk ((g : G₁ d E) : G)) = _
  rw [quot₂_mk]

/-- Step 7: `κ_{G/G₂}[γ̄]` is the transport of `[α₁]` along `ν`. -/
lemma Hyp.kappaElt_quot₂ (x : typEquivs 2 (h.SA : Subgroup (G₁ d E))) (ω : x.1.toFunctor ≅ α₁.fn) :
    kappaElt 2 (quot₂ γ (h.gamma_G₂ hα₁ hγ hfun)) (quot₂_Tbar γ (h.gamma_G₂ hα₁ hγ hfun) hγ) =
      h.fusionHom_ν.typIso.outTyp ((natIsoCon 2 _).mk' x) := by
  rw [TypIso.outTyp_mk, kappaElt]
  apply (natIsoCon 2 _).eq.2
  have e : mapFunctor 2 (quot₂ γ (h.gamma_G₂ hα₁ hγ hfun)) (quot₂_Tbar γ (h.gamma_G₂ hα₁ hγ hfun) hγ) =
      h.fusionHom_ν.bwd ⋙ α₁.fn ⋙ h.fusionHom_ν.fwd := by
    rw [h.ffun hα₁ hγ hfun, ← Functor.assoc, h.fusionHom_ν.bwd_fwd]; rfl
  exact ⟨eqToIso e ≪≫ Functor.isoWhiskerLeft h.fusionHom_ν.bwd
    (Functor.isoWhiskerRight ω.symm h.fusionHom_ν.fwd)⟩

end Good2

end AndersenOliverVentura.Tame
