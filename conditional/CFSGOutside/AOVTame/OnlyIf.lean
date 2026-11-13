import CFSGOutside.AOVTame.TameFactor
import CFSGOutside.AOVTame.OddReduction
import CFSGOutside.AndersenOliverVentura.Paper

/-!
# AOV Theorem 3.8, tameness clause: the "only if" direction

If a reduced fusion system `F = F₁ × F₂` over a 2-group is tame, then `F₁` and `F₂` are tame.

Proof (AOV, proof of Theorem 3.8): by AOV Lemma 2.19 (`tamelyRealizes_quotient`) the tame
realization `G` may be replaced by `G/O(G)`. Goldschmidt's Theorem A (a corpus result, entering as
the class `GoldschmidtTheoremA`) gives commuting normal subgroups `G₁, G₂` with trivial
intersection, `G₁ G₂ ≅ G₁ × G₂` of odd index; `G/G₂` realizes `F₁`, and a splitting of `κ_G`
induces one of `κ_{G/G₂}` (`Hyp.tamelyRealizes₁`).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S S₁ S₂ : Type} [Group S] [Group S₁] [Group S₂] [Finite S]
  {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} {d : ProdData S S₁ S₂}
  {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {E : S →* G}

lemma Hyp.swap (h : Hyp F F₁ F₂ d T E) : Hyp F F₂ F₁ d.swap T E :=
  ⟨h.hS, h.hprod.swap, h.hR, h.hE, h.hr, h.hodd, h.hO2, h.hnorm⟩

/-- In the setting of `Hyp`, the first factor is tame. -/
theorem Hyp.isTame₁ [GoldschmidtTheoremA] [Finite S₁] (h : Hyp F F₁ F₂ d T E)
    {s : OutTyp 2 (T : Subgroup G) →* Out G} (hs : (kappa 2 T).comp s = MonoidHom.id _) :
    IsTame 2 F₁ :=
  ⟨saturated h.quot.1 h.quot.2.1 h.quot.2.2, H d E, inferInstance, inferInstance, Tbar d E T,
    h.tamelyRealizes₁ hs⟩

/-- **AOV Theorem 3.8, tameness clause, "only if".** Let `F` be a reduced fusion system over the
2-group `S₁ × S₂` with `F = F₁ × F₂`. If `F` is tame, then `F₁` and `F₂` are tame. -/
theorem tame_factors [GoldschmidtTheoremA] [Finite S₁] [Finite S₂] (h₁ : IsPGroup 2 S₁)
    (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) (ht : IsTame 2 F) : IsTame 2 F₁ ∧ IsTame 2 F₂ := by
  have hS := isPGroup_prod h₁ h₂
  obtain ⟨-, G, _, _, T, htr⟩ := ht
  obtain ⟨⟨f⟩, s, hs⟩ := tamelyRealizes_quotient hS T htr
  obtain ⟨hE, hr, hR⟩ := realizedBy_of_fusionIso f
  have h : Hyp F F₁ F₂ (ProdData.prod S₁ S₂) _ _ :=
    ⟨hS, hprod.isProdVia, hR, hE, hr, goldschmidtOddCore_quotient_eq_bot,
      oTwo_of_normal hR hE _ hr hred.2.1,
      fun G₀ _ hTG₀ hidx P Q φ hφ => realized_by_normal hE hr hR hTG₀ hred hidx P Q φ hφ⟩
  exact ⟨h.isTame₁ hs, h.swap.isTame₁ hs⟩

end AndersenOliverVentura.Tame
