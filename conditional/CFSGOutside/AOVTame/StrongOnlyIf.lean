import CFSGOutside.AOVTame.OnlyIf
import CFSGOutside.AOVTame.StrongTame

/-!
# AOV Theorem 3.8, strong tameness clause: the "only if" direction

As in the paper, the groups `G/O(G)` and `(G/O(G))/G₂` produced in the proof of `tame_factors` are
quotients of `G`, so they lie in `𝔊(2)` whenever `G` does.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CategoryTheory CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S S₁ S₂ : Type} [Group S] [Group S₁] [Group S₂] [Finite S]
  {F : FusionSystem S} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} {d : ProdData S S₁ S₂}
  {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {E : S →* G}

theorem Hyp.isStronglyTame₁ [GoldschmidtTheoremA] [Finite S₁] (h : Hyp F F₁ F₂ d T E)
    (hG : InGp 2 G) {s : OutTyp 2 (T : Subgroup G) →* Out G}
    (hs : (kappa 2 T).comp s = MonoidHom.id _) : IsStronglyTame 2 F₁ :=
  ⟨saturated h.quot.1 h.quot.2.1 h.quot.2.2, H d E, inferInstance, inferInstance, Tbar d E T,
    hG.quotient _, h.tamelyRealizes₁ hs⟩

/-- **AOV Theorem 3.8, strong tameness clause, "only if".** Let `F` be a reduced fusion system
over the 2-group `S₁ × S₂` with `F = F₁ × F₂`. If `F` is strongly tame, then `F₁` and `F₂` are
strongly tame. -/
theorem stronglyTame_factors [GoldschmidtTheoremA] [Finite S₁] [Finite S₂] (h₁ : IsPGroup 2 S₁)
    (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) (ht : IsStronglyTame 2 F) :
    IsStronglyTame 2 F₁ ∧ IsStronglyTame 2 F₂ := by
  have hS := isPGroup_prod h₁ h₂
  obtain ⟨-, G, _, _, T, hG, htr⟩ := ht
  obtain ⟨⟨f⟩, s, hs⟩ := tamelyRealizes_quotient hS T htr
  obtain ⟨hE, hr, hR⟩ := realizedBy_of_fusionIso f
  have h : Hyp F F₁ F₂ (ProdData.prod S₁ S₂) _ _ :=
    ⟨hS, hprod.isProdVia, hR, hE, hr, goldschmidtOddCore_quotient_eq_bot,
      oTwo_of_normal hR hE _ hr hred.2.1,
      fun G₀ _ hTG₀ hidx P Q φ hφ => realized_by_normal hE hr hR hTG₀ hred hidx P Q φ hφ⟩
  have hG' := hG.quotient (goldschmidtOddCore G)
  exact ⟨h.isStronglyTame₁ hG' hs, h.swap.isStronglyTame₁ hG' hs⟩

end AndersenOliverVentura.Tame
