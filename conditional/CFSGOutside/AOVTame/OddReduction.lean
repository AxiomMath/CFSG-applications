import CFSGOutside.AOVTame.KappaCompat
import CFSGOutside.AOVTame.Defs
import CFSGOutside.AOVTame.Realize
import CFSGOutside.AndersenOliverVentura.OddCore

/-!
# AOV tameness: passing to `G/O(G)` (the case of AOV Lemma 2.19 used in Theorem 3.8)

If `G` tamely realizes `F` over `T ∈ Syl₂(G)`, then so does `G/O(G)` over the image of `T`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

variable {G : Type} [Group G] [Finite G]

lemma map_goldschmidtOddCore (α : MulAut G) :
    (goldschmidtOddCore G).map (α : G →* G) = goldschmidtOddCore G := by
  have key : ∀ β : MulAut G, (goldschmidtOddCore G).map (β : G →* G) ≤ goldschmidtOddCore G := by
    intro β
    apply le_sSup
    refine ⟨(inferInstance : (goldschmidtOddCore G).Normal).map _ β.surjective, ?_⟩
    have : Nat.card ((goldschmidtOddCore G).map (β : G →* G)) = Nat.card (goldschmidtOddCore G) :=
      Nat.card_congr (equivMapOfInjective _ _ β.injective).toEquiv.symm
    rw [this]; exact odd_card_goldschmidtOddCore
  apply le_antisymm (key α)
  intro x hx
  refine ⟨α.symm x, key α.symm ⟨x, hx, rfl⟩, by simp⟩

/-- The automorphism of `G/O(G)` induced by `α ∈ Aut(G)`. -/
def quotAut (α : MulAut G) : MulAut (G ⧸ goldschmidtOddCore G) :=
  QuotientGroup.congr _ _ α (map_goldschmidtOddCore α)

@[simp] lemma quotAut_mk (α : MulAut G) (x : G) :
    quotAut α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  QuotientGroup.congr_mk _ _ _ _ x

/-- `Aut(G) → Aut(G/O(G))`. -/
def quotAutHom : MulAut G →* MulAut (G ⧸ goldschmidtOddCore G) where
  toFun := quotAut
  map_one' := by
    ext y; obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y; simp
  map_mul' α β := by
    ext y; obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y; simp [MulAut.mul_apply]

/-- `Out(G) → Out(G/O(G))`. -/
def quotOut : Out G →* Out (G ⧸ goldschmidtOddCore G) :=
  QuotientGroup.map _ _ quotAutHom (by
    rintro _ ⟨x, rfl⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    ext y; obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    simp [quotAutHom])

/-- The quotient map `G → G/O(G)` is fusion preserving. -/
lemma fusionHom_quotient (T : Sylow 2 G) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    FusionHom 2 T (T.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G)))
      (QuotientGroup.mk' (goldschmidtOddCore G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := goldschmidtOddCore G
  have hT : (T : Subgroup G) ⊓ N = ⊥ := inf_goldschmidtOddCore_eq_bot T.isPGroup'
  refine ⟨Sylow.coe_mapSurjective _ _ |>.symm, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
    have h2 : x⁻¹ * y ∈ (T : Subgroup G) ⊓ N := mem_inf.2 ⟨mul_mem (inv_mem hx) hy, h1⟩
    rw [hT, mem_bot] at h2
    rw [← mul_inv_cancel_left x y, h2, mul_one]
  · intro P hP k hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N k
    have hidx : ¬ 2 ∣ (T : Subgroup G).relIndex N := by
      rw [← inf_relIndex_right, hT, relIndex_bot_left]
      exact (odd_card_goldschmidtOddCore (G := G)).not_two_dvd_nat
    obtain ⟨g', hg', hconj⟩ := exists_lift N T.isPGroup' (T.isPGroup'.to_le hP) hidx g (by
      intro r hr
      have := hk r hr
      rw [Sylow.coe_mapSurjective] at this
      obtain ⟨q, hq, e⟩ := this
      refine ⟨q, hq, ?_⟩
      rw [show (QuotientGroup.mk (g * r * g⁻¹) : G ⧸ N) = QuotientGroup.mk' N g *
        QuotientGroup.mk' N r * (QuotientGroup.mk' N g)⁻¹ by simp]
      exact e.symm)
    refine ⟨g', hconj, fun x hx => ?_⟩
    simp only [map_mul, map_inv]
    rw [show QuotientGroup.mk' N g' = QuotientGroup.mk' N g from hg']

section
attribute [local instance] Nat.fact_prime_two

lemma kappa_quotOut (T : Sylow 2 G) (z : Out G) :
    kappa 2 (T.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G))) (quotOut z) =
      (fusionHom_quotient T).typIso.outTyp (kappa 2 T z) := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective z
  set N := goldschmidtOddCore G
  set π := QuotientGroup.mk' N
  obtain ⟨g, hg⟩ := exists_map_eq_conjSub 2 T α
  set T' := T.mapSurjective (QuotientGroup.mk'_surjective N)
  have hT' : (T' : Subgroup (G ⧸ N)) = (T : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  have hg' : (T' : Subgroup (G ⧸ N)).map (quotAut α : _ →* _) = conjSub (π g) T' := by
    rw [hT', map_map]
    have : ((quotAut α : _ →* _).comp π) = π.comp α.toMonoidHom := by
      ext x; exact quotAut_mk α x
    rw [this, ← map_map, hg]
    exact (fusionHom_quotient T).map_conjSub g
  change kappaAut 2 T' (quotAut α) = (fusionHom_quotient T).typIso.outTyp (kappaAut 2 T α)
  rw [kappaAut_eq 2 T' _ _ hg', kappaAut_eq 2 T _ _ hg]
  symm
  apply (fusionHom_quotient T).outTyp_kappaElt
  intro x
  rw [MulAut.mul_apply, MulAut.mul_apply]
  change π ((MulAut.conj g)⁻¹ (α x)) = (MulAut.conj (π g))⁻¹ (quotAut α (π x))
  rw [show quotAut α (π x) = π (α x) from quotAut_mk α x]
  simp only [MulAut.inv_def, MulAut.conj_symm_apply, map_mul, map_inv]

/-- If `G` tamely realizes `F` over `T`, so does `G/O(G)` over the image of `T`. -/
theorem tamelyRealizes_quotient {S : Type*} [Group S] (hS : IsPGroup 2 S) {F : FusionSystem S}
    (T : Sylow 2 G) (h : TamelyRealizes 2 F G T) :
    TamelyRealizes 2 F (G ⧸ goldschmidtOddCore G)
      (T.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G))) := by
  obtain ⟨⟨f⟩, s, hs⟩ := h
  obtain ⟨hE, hr, hR⟩ := realizedBy_of_fusionIso f
  obtain ⟨T'', hE', hr', hR'⟩ := realizedBy_quotient_oddCore hS T hE hr hR
  have hT'' : T'' = T.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G)) := by
    apply Sylow.ext
    rw [← hr', MonoidHom.range_comp, hr, Sylow.coe_mapSurjective]
  subst hT''
  refine ⟨fusionIso_of_realizedBy hE' hr' hR', quotOut.comp (s.comp
    (fusionHom_quotient T).typIso.symm.outTyp), ?_⟩
  refine MonoidHom.ext fun y => ?_
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  rw [kappa_quotOut]
  have := congrArg (fun φ => φ ((fusionHom_quotient T).typIso.symm.outTyp y)) hs
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at this
  rw [this, TypIso.outTyp_outTyp_symm]

end

end AndersenOliverVentura.Tame
