import CFSGOutside.AOVTame.GoodBasic
import CFSGOutside.AOVTame.OnlyIf
import CFSGOutside.AOVTame.DecompProd

/-!
# AOV tameness: the minimal direct factors of a product of tame realizations are tame

Let `G₁, G₂` tamely realize `F₁, F₂` with `O(Gᵢ) = 1`, and let `X` be a minimal direct factor of
`T₁ × T₂` in `G₁ × G₂` (with `Good`). Then `X` lies in one factor, say `T₁`, where it is a direct
factor of `T₁` in `G₁`; the "only if" construction (`Hyp.tamelyRealizes₁`) shows that `F_X` is
tame.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

lemma TamelyRealizes.of_iso {S S' : Type*} [Group S] [Group S'] {p : ℕ} [Fact p.Prime]
    {F : FusionSystem S} {F' : FusionSystem S'} {G : Type} [Group G] [Finite G] {T : Sylow p G}
    (h : TamelyRealizes p F G T) (f : FusionIso F' F) : TamelyRealizes p F' G T :=
  let ⟨⟨g⟩, hs⟩ := h; ⟨⟨f.trans g⟩, hs⟩

lemma Good.hnorm {G : Type} [Group G] [Finite G] {T : Sylow 2 G} (hG : Good T) :
    ∀ G₀ : Subgroup G, G₀.Normal → (T : Subgroup G) ≤ G₀ → ¬ 2 ∣ G₀.index →
      ∀ (P Q : Subgroup (T : Subgroup G)) (φ : P →* Q), φ ∈ (ofGroup G (T : Subgroup G)).hom P Q →
        ∃ g ∈ G₀, ∀ x : P, (T : Subgroup G).subtype (φ x) =
          g * (T : Subgroup G).subtype x * g⁻¹ := by
  rintro G₀ hN hT hidx P Q φ ⟨g, hg⟩
  have hP : P.map (T : Subgroup G).subtype ≤ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hPg : (P.map (T : Subgroup G).subtype).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [inv_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    change g * (x : G) * g⁻¹ ∈ (T : Subgroup G)
    rw [← hg ⟨x, hx⟩]; exact (φ ⟨x, hx⟩ : (T : Subgroup G)).2
  obtain ⟨g₀, hg₀, hx⟩ := hG.norm G₀ hN hT hidx _ hP g⁻¹ hPg
  refine ⟨g₀⁻¹, inv_mem hg₀, fun x => ?_⟩
  have := hx _ ⟨x, x.2, rfl⟩
  rw [inv_inv] at this
  simp only [coe_subtype]
  rw [hg x, inv_inv]
  exact this.symm

section Retract
variable {A P : Type} [Group A] [Group P] [Finite A] [Finite P] {SA : Sylow 2 A} {TP : Sylow 2 P}
  (ι : A →* P) (π : P →* A) (hπι : ∀ a, π (ι a) = a)
  (hιS : (SA : Subgroup A).map ι ≤ TP) (hπT : (TP : Subgroup P).map π ≤ SA)
include hπι hιS hπT

/-- A direct factor of `T_P` inside `ι(S_A)` comes from a direct factor of `S_A`. -/
lemma Decomp.comap_retract {Z C : Subgroup P} (h : Decomp TP Z C)
    (hZ : Z ≤ (SA : Subgroup A).map ι) : Decomp SA (Z.comap ι) (C.comap ι) where
  leX a ha := by
    obtain ⟨s, hs, e⟩ := hZ ha
    rw [← retract_injective ι π hπι e]; exact hs
  leY a ha := by
    have := hπT ⟨ι a, h.leY ha, rfl⟩
    rwa [hπι] at this
  inf := by
    rw [← comap_inf, h.inf]
    ext a
    simp only [mem_comap, mem_bot]
    exact ⟨fun e => retract_injective ι π hπι (e.trans (map_one ι).symm), fun e => by
      rw [e, map_one]⟩
  comm x hx y hy := retract_injective ι π hπι (by
    rw [map_mul, map_mul]; exact h.comm _ hx _ hy)
  sup s hs := by
    obtain ⟨z, hz, c, hc, e⟩ := h.sup (ι s) (hιS ⟨s, hs, rfl⟩)
    obtain ⟨s₁, -, rfl⟩ := hZ hz
    refine ⟨s₁, hz, s₁⁻¹ * s, ?_, by group⟩
    show ι (s₁⁻¹ * s) ∈ C
    rw [map_mul, map_inv, e]
    simpa using hc
  scX a ha g hg := by
    have : (ι g)⁻¹ * ι a * ι g ∈ Z := h.scX (ι a) ha (ι g) (by
      rw [← map_inv, ← map_mul, ← map_mul]; exact hιS ⟨_, hg, rfl⟩)
    show ι (g⁻¹ * a * g) ∈ Z
    simpa using this
  scY a ha g hg := by
    have : (ι g)⁻¹ * ι a * ι g ∈ C := h.scY (ι a) ha (ι g) (by
      rw [← map_inv, ← map_mul, ← map_mul]; exact hιS ⟨_, hg, rfl⟩)
    show ι (g⁻¹ * a * g) ∈ C
    simpa using this

variable (hconj : ∀ g a, g * ι a * g⁻¹ = ι (π g * a * (π g)⁻¹))
include hconj

/-- **A direct factor inside a retract with a tame realization is tame.** -/
theorem tame_of_retract [GoldschmidtTheoremA] (hP : Good TP) (hodd : goldschmidtOddCore A = ⊥)
    {s : OutTyp 2 (SA : Subgroup A) →* Out A} (hs : (kappa 2 SA).comp s = MonoidHom.id _)
    {Z C : Subgroup P} (h : Decomp TP Z C) (hZ : Z ≤ (SA : Subgroup A).map ι) :
    ∃ (N : Subgroup A) (_ : N.Normal) (S : Sylow 2 (A ⧸ N)),
      TamelyRealizes 2 (ofGroup P Z) (A ⧸ N) S := by
  have hA := hP.retract ι π hπι hconj hιS hπT hodd
  have hd := Decomp.comap_retract ι π hπι hιS hπT h hZ
  have hyp : Hyp (ofGroup A (SA : Subgroup A)) (ofGroup A (Z.comap ι)) (ofGroup A (C.comap ι))
      hd.prodData SA (SA : Subgroup A).subtype :=
    ⟨SA.isPGroup', hd.isProdVia hA, realizedBy_subtype' _, subtype_injective _, range_subtype _,
      hodd, hA.two, hA.hnorm⟩
  have ht := hyp.tamelyRealizes₁ hs
  have hR := realizedBy_retract ι π hπι hconj (Z.comap ι)
  have hrange : (ι.comp (Z.comap ι).subtype).range = Z := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy
      obtain ⟨s, -, rfl⟩ := hZ hy
      exact ⟨⟨s, hy⟩, rfl⟩
  obtain ⟨f⟩ := fusionIso_of_realizedBy
    (show Function.Injective (ι.comp (Z.comap ι).subtype) from
      fun a b e => Subtype.ext (retract_injective ι π hπι e)) hrange hR
  exact ⟨_, inferInstance, _, ht.of_iso f.symm⟩

end Retract

section Prod
variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

/-- `T_A × T_B = (T_A × 1) × (1 × T_B)` in `A × B`. -/
lemma decomp_prod (SA : Sylow 2 A) (SB : Sylow 2 B) :
    Decomp (prodSylow SA SB) ((SA : Subgroup A).map (MonoidHom.inl A B))
      ((SB : Subgroup B).map (MonoidHom.inr A B)) where
  leX := by rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, one_mem _⟩
  leY := by rintro _ ⟨b, hb, rfl⟩; exact ⟨one_mem _, hb⟩
  inf := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, -, rfl⟩, ⟨b, -, e⟩⟩
    have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    simp only [MonoidHom.inr_apply, MonoidHom.inl_apply] at h1 h2
    rw [mem_bot]
    ext
    · simp [← h1]
    · simp
  comm := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    ext <;> simp
  sup := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, by ext <;> simp⟩
  scX := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    refine ⟨g.1⁻¹ * a * g.1, ?_, ?_⟩
    · have := hg.1
      simpa using this
    · ext <;> simp
  scY := by
    rintro _ ⟨b, hb, rfl⟩ g hg
    refine ⟨g.2⁻¹ * b * g.2, ?_, ?_⟩
    · have := hg.2
      simpa using this
    · ext <;> simp

/-- **Minimal factors of `T₁ × T₂` are tame**, realized by a quotient of `A` or of `B` (so any
property of `A` and `B` inherited by quotients holds for the realizing group). -/
theorem tame_minFactor_prod' [GoldschmidtTheoremA] (Pr : ∀ (H : Type) [Group H], Prop)
    (hPA : Pr A) (hPB : Pr B)
    (hPq : ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal], Pr H → Pr (H ⧸ N))
    {T₁ : Sylow 2 A} {T₂ : Sylow 2 B}
    (hG : Good (prodSylow T₁ T₂)) (h₁ : goldschmidtOddCore A = ⊥) (h₂ : goldschmidtOddCore B = ⊥)
    {s₁ : OutTyp 2 (T₁ : Subgroup A) →* Out A} (hs₁ : (kappa 2 T₁).comp s₁ = MonoidHom.id _)
    {s₂ : OutTyp 2 (T₂ : Subgroup B) →* Out B} (hs₂ : (kappa 2 T₂).comp s₂ = MonoidHom.id _)
    {X : Subgroup (A × B)} (hX : IsMinFactor (prodSylow T₁ T₂) X) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (S : Sylow 2 H),
      Pr H ∧ TamelyRealizes 2 (ofGroup (A × B) X) H S := by
  obtain ⟨C, hC⟩ := hX.1
  rcases hX.le_or hG (decomp_prod T₁ T₂) with h | h
  · obtain ⟨N, hN, S, ht⟩ := tame_of_retract (MonoidHom.inl A B) (MonoidHom.fst A B) inl_retract
      (by rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, one_mem _⟩)
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.1) inl_conj hG h₁ hs₁ hC h
    exact ⟨_, inferInstance, inferInstance, S, hPq A N hPA, ht⟩
  · obtain ⟨N, hN, S, ht⟩ := tame_of_retract (MonoidHom.inr A B) (MonoidHom.snd A B) inr_retract
      (by rintro _ ⟨b, hb, rfl⟩; exact ⟨one_mem _, hb⟩)
      (by rintro _ ⟨x, hx, rfl⟩; exact hx.2) inr_conj hG h₂ hs₂ hC h
    exact ⟨_, inferInstance, inferInstance, S, hPq B N hPB, ht⟩

/-- **Minimal factors of `T₁ × T₂` are tame.** -/
theorem tame_minFactor_prod [GoldschmidtTheoremA] {T₁ : Sylow 2 A} {T₂ : Sylow 2 B}
    (hG : Good (prodSylow T₁ T₂)) (h₁ : goldschmidtOddCore A = ⊥) (h₂ : goldschmidtOddCore B = ⊥)
    {s₁ : OutTyp 2 (T₁ : Subgroup A) →* Out A} (hs₁ : (kappa 2 T₁).comp s₁ = MonoidHom.id _)
    {s₂ : OutTyp 2 (T₂ : Subgroup B) →* Out B} (hs₂ : (kappa 2 T₂).comp s₂ = MonoidHom.id _)
    {X : Subgroup (A × B)} (hX : IsMinFactor (prodSylow T₁ T₂) X) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (S : Sylow 2 H),
      TamelyRealizes 2 (ofGroup (A × B) X) H S := by
  obtain ⟨H, i1, i2, S, -, ht⟩ := tame_minFactor_prod' (fun _ _ => True) trivial trivial
    (fun _ _ _ _ _ => trivial) hG h₁ h₂ hs₁ hs₂ hX
  exact ⟨H, i1, i2, S, ht⟩

end Prod

end AndersenOliverVentura.Tame
