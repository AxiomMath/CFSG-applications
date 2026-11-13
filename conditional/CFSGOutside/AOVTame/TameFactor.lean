import CFSGOutside.AOVTame.Split
import CFSGOutside.AOVTame.Defs
import CFSGOutside.AOVTame.Saturation
import CFSGOutside.AOVTame.Realize

/-!
# AOV tameness: a tame realization of `F₁ × F₂` gives one of `F₁`

In the setting of `Setup`, a splitting `s` of `κ_G` induces a splitting of `κ_{G/G₂}`:
`[α] ↦ [γ̄]`, where `γ ∈ s(Ψ(α × Id))` is the representative of `Split`, which normalizes `G₂`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S S₁ S₂ : Type} [Group S] [Group S₁] [Group S₂] [Finite S]
  {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} {d : ProdData S S₁ S₂}
  {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {E : S →* G}

/-- The automorphisms of `G` normalizing `G₂`. -/
def stab₂ (d : ProdData S S₁ S₂) (E : S →* G) : Subgroup (MulAut G) where
  carrier := {γ | (G₂ d E).map γ.toMonoidHom = G₂ d E}
  one_mem' := by
    show (G₂ d E).map (1 : MulAut G).toMonoidHom = _
    ext x; simp
  mul_mem' := by
    intro a b ha hb
    show (G₂ d E).map (a * b).toMonoidHom = _
    rw [map_mul_toMonoidHom, hb, ha]
  inv_mem' := by
    intro a ha
    show (G₂ d E).map a⁻¹.toMonoidHom = _
    conv_lhs => rw [← ha]
    rw [← map_mul_toMonoidHom, inv_mul_cancel]
    ext x; simp

lemma quot₂_mk' (γ : stab₂ d E) (x : G) :
    quot₂ γ.1 γ.2 (QuotientGroup.mk x : H d E) = QuotientGroup.mk (γ.1 x) :=
  quot₂_mk _ _ x

/-- `Aut(G, G₂) → Aut(G/G₂)`. -/
def rho₂ (d : ProdData S S₁ S₂) (E : S →* G) : stab₂ d E →* MulAut (H d E) where
  toFun γ := quot₂ γ.1 γ.2
  map_one' := by
    ext y; obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quot₂_mk' 1]; rfl
  map_mul' a b := by
    ext y; obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [MulAut.mul_apply]
    rw [quot₂_mk' (a * b), quot₂_mk' b, quot₂_mk' a]; rfl

/-- `Aut(G, G₂) → Out(G)`. -/
def qN (d : ProdData S S₁ S₂) (E : S →* G) : stab₂ d E →* Out G :=
  (QuotientGroup.mk' _).comp (stab₂ d E).subtype

/-- `Aut(G, G₂) → Out(G/G₂)`. -/
def outH (d : ProdData S S₁ S₂) (E : S →* G) : stab₂ d E →* Out (H d E) :=
  (QuotientGroup.mk' _).comp (rho₂ d E)

lemma ker_qN_le : (qN d E).ker ≤ (outH d E).ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker, qN, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hγ
  obtain ⟨g, hg⟩ := hγ
  rw [MonoidHom.mem_ker, outH, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  refine ⟨QuotientGroup.mk g, ?_⟩
  ext y; obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  change _ = quot₂ γ.1 γ.2 _
  rw [quot₂_mk', ← show (MulAut.conj g : MulAut G) = γ.1 from hg]
  simp

/-- The image of `Aut(G, G₂)` in `Out(G)` maps to `Out(G/G₂)`. -/
noncomputable def rhoBar (d : ProdData S S₁ S₂) (E : S →* G) : (qN d E).range →* Out (H d E) :=
  (QuotientGroup.lift _ (outH d E) ker_qN_le).comp
    (QuotientGroup.quotientKerEquivRange (qN d E)).symm.toMonoidHom

lemma rhoBar_apply (γ : stab₂ d E) : rhoBar d E ⟨qN d E γ, γ, rfl⟩ = outH d E γ := by
  have : (QuotientGroup.quotientKerEquivRange (qN d E)).symm ⟨qN d E γ, γ, rfl⟩ =
      QuotientGroup.mk γ := by
    rw [MulEquiv.symm_apply_eq]; rfl
  change QuotientGroup.lift _ (outH d E) ker_qN_le
    ((QuotientGroup.quotientKerEquivRange (qN d E)).symm ⟨qN d E γ, γ, rfl⟩) = _
  rw [this]; rfl

section
variable [GoldschmidtTheoremA] (h : Hyp F F₁ F₂ d T E)
include h

/-- `Ψ : Out_typ(L(G/G₂)) → Out_typ(L(G))`, `[α] ↦ [α × Id]`, transported along `ν` and `μ`. -/
noncomputable def Hyp.Θ : OutTyp 2 (Tbar d E T : Subgroup (H d E)) →* OutTyp 2 (T : Subgroup G) :=
  h.fusionHom_μ.typIso.outTyp.comp ((phiBar h.SB).comp h.fusionHom_ν.typIso.symm.outTyp)

variable {s : OutTyp 2 (T : Subgroup G) →* Out G} (hs : (kappa 2 T).comp s = MonoidHom.id _)
include hs

lemma Hyp.core (α : OutTyp 2 (Tbar d E T : Subgroup (H d E))) :
    ∃ (γ : MulAut G) (hst : γ ∈ stab₂ d E) (hγ : (T : Subgroup G).map γ.toMonoidHom = T),
      (QuotientGroup.mk γ : Out G) = s (h.Θ α) ∧
      kappaElt 2 (quot₂ γ hst) (quot₂_Tbar γ hst hγ) = α := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep (h.fusionHom_ν.typIso.symm.outTyp α)
  have hx' : (natIsoCon 2 _).mk' x = h.fusionHom_ν.typIso.symm.outTyp α := hx
  set α₁ := repAut x
  have hα₁ := repAut_mem x
  obtain ⟨ω₁⟩ := repAut_iso x
  have hΘ : h.Θ α = (natIsoCon 2 _).mk' ⟨(h.fusionHom_μ.conjAut (phiAut h.SB hα₁)).hom, by
      have := h.fusionHom_μ.typIso.conj_mem (x := (phiAut h.SB hα₁).hom) (by
        haveI := phiFunctor_isIso (SB := h.SB) hα₁
        exact ⟨(inferInstance : (phiFunctor h.SB hα₁).IsEquivalence), phiFunctor_isIsotypical hα₁⟩)
      exact this⟩ := by
    rw [Hyp.Θ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hx', phiBar_mk hα₁ x ω₁]
    rfl
  -- a representative `γ₀ ∈ Aut(G, T)` of `s(Θ α)`
  obtain ⟨γ', hγ'⟩ := QuotientGroup.mk_surjective (s (h.Θ α))
  obtain ⟨g, hg⟩ := exists_map_eq_conjSub 2 T γ'
  set γ₀ := (MulAut.conj g)⁻¹ * γ'
  have hγ₀ := conj_inv_mul_mem 2 T γ' hg
  have hmk₀ : (QuotientGroup.mk γ₀ : Out G) = s (h.Θ α) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (inv_mem (MonoidHom.mem_range.2 ⟨g, rfl⟩)),
      one_mul]
    exact hγ'
  have hκ : kappaElt 2 γ₀ hγ₀ = h.Θ α := by
    rw [← kappa_mk, hmk₀]
    exact DFunLike.congr_fun hs (h.Θ α)
  rw [hΘ, kappaElt] at hκ
  have ω := (natIsoCon 2 _).eq.1 hκ
  obtain ⟨γ, hγ, hmk, hfun⟩ := h.exists_good hα₁ γ₀ hγ₀ ω
  refine ⟨γ, h.gamma_G₂ hα₁ hγ hfun, hγ, hmk.trans hmk₀, ?_⟩
  rw [h.kappaElt_quot₂ hα₁ hγ hfun x ω₁, hx', TypIso.outTyp_outTyp_symm]

/-- The splitting of `κ_{G/G₂}`. -/
noncomputable def Hyp.split₁ : OutTyp 2 (Tbar d E T : Subgroup (H d E)) →* Out (H d E) :=
  (rhoBar d E).comp ((s.comp h.Θ).codRestrict (qN d E).range (fun α => by
    obtain ⟨γ, hst, -, hmk, -⟩ := h.core hs α
    exact ⟨⟨γ, hst⟩, hmk⟩))

lemma Hyp.split₁_spec : (kappa 2 (Tbar d E T)).comp (h.split₁ hs) = MonoidHom.id _ := by
  refine MonoidHom.ext fun α => ?_
  obtain ⟨γ, hst, hγ, hmk, hκ⟩ := h.core hs α
  have e : ((s.comp h.Θ).codRestrict (qN d E).range (fun α => by
      obtain ⟨γ, hst, -, hmk, -⟩ := h.core hs α
      exact ⟨⟨γ, hst⟩, hmk⟩) α : (qN d E).range) = ⟨qN d E ⟨γ, hst⟩, ⟨γ, hst⟩, rfl⟩ :=
    Subtype.ext hmk.symm
  change kappa 2 (Tbar d E T) (rhoBar d E _) = α
  rw [e, rhoBar_apply]
  change kappa 2 (Tbar d E T) (QuotientGroup.mk (quot₂ γ hst)) = α
  rw [kappa_mk 2 (Tbar d E T) _ (quot₂_Tbar γ hst hγ), hκ]

/-- `G/G₂` tamely realizes `F₁`. -/
theorem Hyp.tamelyRealizes₁ : TamelyRealizes 2 F₁ (H d E) (Tbar d E T) :=
  ⟨fusionIso_of_realizedBy h.quot.1 h.quot.2.1 h.quot.2.2, h.split₁ hs, h.split₁_spec hs⟩

end

end AndersenOliverVentura.Tame
