import CFSGOutside.AOVTame.TameIf
import CFSGOutside.AOVTame.GpProd
import CFSGOutside.AOVTame.StrongOnlyIf

/-!
# AOV Theorem 3.8, strong tameness clause: the "if" direction

The proof of `tame_product` produces a tame realization by `∏_c H_c^{ι_c}`, where each `H_c` is a
quotient of `Gᵢ/O(Gᵢ)` for a tame realization `Gᵢ` of `Fᵢ`. If the `Gᵢ` lie in `𝔊(2)`, so do their
quotients (`InGp.quotient`) and finite products of these (`inGp_pi_fin`, AOV Lemma 2.11(b)).
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S₁ S₂ : Type} [Group S₁] [Group S₂] {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}

/-- **AOV Theorem 3.8, strong tameness clause, "if".** Let `F` be a reduced fusion system over the
2-group `S₁ × S₂` with `F = F₁ × F₂`. If `F₁` and `F₂` are strongly tame, then `F` is strongly
tame. -/
theorem stronglyTame_product [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) (t₁ : IsStronglyTame 2 F₁) (t₂ : IsStronglyTame 2 F₂) :
    IsStronglyTame 2 F := by
  obtain ⟨-, G₁, _, _, T₁, hG₁, htr₁⟩ := t₁
  obtain ⟨-, G₂, _, _, T₂, hG₂, htr₂⟩ := t₂
  obtain ⟨⟨f₁⟩, s₁, hs₁⟩ := tamelyRealizes_quotient h₁ T₁ htr₁
  obtain ⟨⟨f₂⟩, s₂, hs₂⟩ := tamelyRealizes_quotient h₂ T₂ htr₂
  set TA := T₁.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G₁))
  set TB := T₂.mapSurjective (QuotientGroup.mk'_surjective (goldschmidtOddCore G₂))
  obtain ⟨hE₁, hr₁, hR₁⟩ := realizedBy_of_fusionIso f₁
  obtain ⟨hE₂, hr₂, hR₂⟩ := realizedBy_of_fusionIso f₂
  set E := MonoidHom.prodMap ((TA : Subgroup (G₁ ⧸ goldschmidtOddCore G₁)).subtype.comp
    f₁.toMulEquiv.toMonoidHom)
    ((TB : Subgroup (G₂ ⧸ goldschmidtOddCore G₂)).subtype.comp f₂.toMulEquiv.toMonoidHom)
  have hE : Function.Injective E := Prod.map_injective.2 ⟨hE₁, hE₂⟩
  have hr : E.range = ((prodSylow TA TB : Sylow 2 _) : Subgroup (_ × _)) := by
    rw [MonoidHom.range_prodMap, hr₁, hr₂]; rfl
  have hR := realizedBy_prodMap hprod hE₁ hE₂ hR₁ hR₂
  have hG := good_of_reduced hE hr hR hred
    (goldschmidtOddCore_prod goldschmidtOddCore_quotient_eq_bot goldschmidtOddCore_quotient_eq_bot)
  have hq : ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal], InGp 2 H → InGp 2 (H ⧸ N) :=
    fun _ _ N _ h => InGp.quotient (N := N) h
  obtain ⟨G', _, _, T', hG', htr⟩ := tamelyRealizes_of_minFactors' hG (fun H _ => InGp 2 H)
    (fun m bs h => inGp_pi_fin m _ (fun i => (h i).pow _)) (fun X =>
      tame_minFactor_prod' (fun H _ => InGp 2 H) (hq _ _ hG₁) (hq _ _ hG₂) hq hG
        goldschmidtOddCore_quotient_eq_bot goldschmidtOddCore_quotient_eq_bot hs₁ hs₂ X.2)
  exact ⟨hred.1, G', inferInstance, inferInstance, T', hG', htr.of_iso (isoOfRealized hE hr hR)⟩

/-- **AOV Theorem 3.8, strong tameness clause.** A reduced `F = F₁ × F₂` over a 2-group
`S₁ × S₂` is strongly tame if and only if `F₁` and `F₂` are strongly tame. -/
theorem theorem_3_8_stronglyTame [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) :
    IsStronglyTame 2 F ↔ IsStronglyTame 2 F₁ ∧ IsStronglyTame 2 F₂ :=
  ⟨stronglyTame_factors h₁ h₂ hred hprod,
    fun ⟨t₁, t₂⟩ => stronglyTame_product h₁ h₂ hred hprod t₁ t₂⟩

end AndersenOliverVentura.Tame
