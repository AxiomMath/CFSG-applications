import CFSGOutside.AOVTame.Assemble

/-!
# AOV Theorem 3.8, tameness clause: the "if" direction

Let `F` be a reduced fusion system over the 2-group `S₁ × S₂` with `F = F₁ × F₂`. If `F₁` and `F₂`
are tame, then `F` is tame.

Proof: realize `F` by `G = G₁/O(G₁) × G₂/O(G₂)` for tame realizations `Gᵢ` of `Fᵢ`. Then `G`
satisfies `Good` (from reducedness), every minimal direct factor of `T` is tame
(`tame_minFactor_prod`), and AOV Theorem 3.7 (`tamelyRealizes_of_minFactors`) gives a tame
realization of `F_T(G) ≅ F`.
-/

namespace AndersenOliverVentura.Tame

open Subgroup CFSGOutside.Corpus

attribute [local instance] Nat.fact_prime_two

variable {S₁ S₂ : Type} [Group S₁] [Group S₂] {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}

/-- A product of realizations realizes the product fusion system. -/
lemma realizedBy_prodMap {F : FusionSystem (S₁ × S₂)} (hprod : IsProduct F F₁ F₂) {G₁ G₂ : Type}
    [Group G₁] [Group G₂] {E₁ : S₁ →* G₁} {E₂ : S₂ →* G₂} (hE₁ : Function.Injective E₁)
    (hE₂ : Function.Injective E₂) (hR₁ : RealizedBy F₁ E₁) (hR₂ : RealizedBy F₂ E₂) :
    RealizedBy F (E₁.prodMap E₂) := by
  intro P Q φ
  constructor
  · intro hφ
    obtain ⟨φ₁, hφ₁, φ₂, hφ₂, hx⟩ := (hprod P Q φ).1 hφ
    obtain ⟨g₁, hg₁⟩ := (hR₁ _ _ φ₁).1 hφ₁
    obtain ⟨g₂, hg₂⟩ := (hR₂ _ _ φ₂).1 hφ₂
    refine ⟨(g₁, g₂), fun x => ?_⟩
    rw [hx x]
    exact Prod.ext (hg₁ _) (hg₂ _)
  · rintro ⟨⟨g₁, g₂⟩, hg⟩
    have hg' : ∀ x : P, E₁ (φ x : S₁ × S₂).1 = g₁ * E₁ (x : S₁ × S₂).1 * g₁⁻¹ ∧
        E₂ (φ x : S₁ × S₂).2 = g₂ * E₂ (x : S₁ × S₂).2 * g₂⁻¹ := fun x =>
      Prod.ext_iff.1 (hg x)
    obtain ⟨φ₁, hφ₁, hφ₁e⟩ := hR₁.exists_mem hE₁ (P := P.map (MonoidHom.fst S₁ S₂))
      (Q := Q.map (MonoidHom.fst S₁ S₂)) g₁ (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨_, mem_map_of_mem _ (φ ⟨x, hx⟩).2, (hg' ⟨x, hx⟩).1⟩)
    obtain ⟨φ₂, hφ₂, hφ₂e⟩ := hR₂.exists_mem hE₂ (P := P.map (MonoidHom.snd S₁ S₂))
      (Q := Q.map (MonoidHom.snd S₁ S₂)) g₂ (by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨_, mem_map_of_mem _ (φ ⟨x, hx⟩).2, (hg' ⟨x, hx⟩).2⟩)
    refine (hprod P Q φ).2 ⟨φ₁, hφ₁, φ₂, hφ₂, fun x => Prod.ext (hE₁ ?_) (hE₂ ?_)⟩
    · rw [(hg' x).1, hφ₁e]
    · rw [(hg' x).2, hφ₂e]

/-- **AOV Theorem 3.8, tameness clause, "if".** Let `F` be a reduced fusion system over the
2-group `S₁ × S₂` with `F = F₁ × F₂`. If `F₁` and `F₂` are tame, then `F` is tame. -/
theorem tame_product [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) (t₁ : IsTame 2 F₁) (t₂ : IsTame 2 F₂) : IsTame 2 F := by
  obtain ⟨-, G₁, _, _, T₁, htr₁⟩ := t₁
  obtain ⟨-, G₂, _, _, T₂, htr₂⟩ := t₂
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
  obtain ⟨G', _, _, T', htr⟩ := tamelyRealizes_of_minFactors hG (fun X =>
    tame_minFactor_prod hG goldschmidtOddCore_quotient_eq_bot goldschmidtOddCore_quotient_eq_bot
      hs₁ hs₂ X.2)
  exact ⟨hred.1, G', inferInstance, inferInstance, T', htr.of_iso (isoOfRealized hE hr hR)⟩

/-- **Tame fusion systems.** Let F = F₁ × F₂ be a reduced fusion system over S₁ × S₂, where F₁ and F₂ are fusion systems
over finite 2-groups S₁ and S₂. Then F is realizable by a finite group if and only if F₁ and F₂ are, F is tame if
and only if F₁ and F₂ are, and F is strongly tame if and only if F₁ and F₂ are.

Source: K. K. S. Andersen, B. Oliver, J. Ventura, Reduced, tame and exotic fusion systems, Proc. London Math. Soc.
(3) 105 (2012), 87–152, Theorem 3.8. https://doi.org/10.1112/plms/pdr065

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_3_8_tame [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) : IsTame 2 F ↔ IsTame 2 F₁ ∧ IsTame 2 F₂ :=
  ⟨tame_factors h₁ h₂ hred hprod, fun ⟨t₁, t₂⟩ => tame_product h₁ h₂ hred hprod t₁ t₂⟩

end AndersenOliverVentura.Tame
