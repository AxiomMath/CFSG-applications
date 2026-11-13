import CFSGOutside.AndersenOliverVentura.Factor

/-!
# Andersen–Oliver–Ventura, Theorem 3.8: the realizability clause

K. K. S. Andersen, B. Oliver, J. Ventura, *Reduced, tame and exotic fusion systems*,
Proc. London Math. Soc. (3) 105 (2012), 87–152, DOI 10.1112/plms/pdr065; Theorem 3.8 of
arXiv:1009.0622 (§3, p. 51):

> Assume `p = 2`, and let `F` be a reduced fusion system over a 2-group `S`. Assume `F = F₁ × F₂`,
> where `Fᵢ` is a fusion system over `Sᵢ` and `S = S₁ × S₂`. Then `F` is realizable, tame, or
> strongly tame if and only if `F₁` and `F₂` are both realizable, tame, or strongly tame,
> respectively.

This file proves the **realizability clause** (a special case: the tame and strongly tame
clauses are not formalized), conditional on Goldschmidt's Theorem A
(`CFSGOutside.Corpus.GoldschmidtTheoremA`). The "only if" direction needs only that `F` has no
nontrivial normal 2-subgroup (`realizable_factors`); the "if" direction holds for every product
(`realizable_product`).
-/

namespace AndersenOliverVentura

open Subgroup CFSGOutside.Corpus

universe u v

lemma isPGroup_prod {p : ℕ} {S₁ : Type u} {S₂ : Type v} [Group S₁] [Group S₂]
    (h₁ : IsPGroup p S₁) (h₂ : IsPGroup p S₂) : IsPGroup p (S₁ × S₂) := by
  rintro ⟨a, b⟩
  obtain ⟨i, hi⟩ := h₁ a
  obtain ⟨j, hj⟩ := h₂ b
  refine ⟨i + j, Prod.ext ?_ ?_⟩
  · simp only [Prod.pow_fst, Prod.fst_one, pow_add, pow_mul, hi, one_pow]
  · simp only [Prod.pow_snd, Prod.snd_one, pow_add, mul_comm (p ^ i), pow_mul, hj, one_pow]

/-- The "if" half: a product of realizable fusion systems is realizable (AOV §3: for groups `Gᵢ`
with `Sᵢ ∈ Syl_p(Gᵢ)`, `F_{S₁×S₂}(G₁×G₂) = F_{S₁}(G₁) × F_{S₂}(G₂)`). -/
theorem realizable_product {p : ℕ} [Fact p.Prime] {S₁ : Type u} {S₂ : Type v} [Group S₁]
    [Group S₂] {F : FusionSystem (S₁ × S₂)} {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}
    (hprod : IsProduct F F₁ F₂) (h₁ : Realizable p F₁) (h₂ : Realizable p F₂) :
    Realizable p F := by
  obtain ⟨G₁, _, _, T₁, E₁, hE₁, hr₁, hR₁⟩ := (realizable_iff p F₁).1 h₁
  obtain ⟨G₂, _, _, T₂, E₂, hE₂, hr₂, hR₂⟩ := (realizable_iff p F₂).1 h₂
  let T₀ : Subgroup (G₁ × G₂) := (T₁ : Subgroup G₁).prod T₂
  have hT₀ : IsPGroup p T₀ := by
    rintro ⟨⟨a, b⟩, ha, hb⟩
    obtain ⟨i, hi⟩ := T₁.isPGroup' ⟨a, ha⟩
    obtain ⟨j, hj⟩ := T₂.isPGroup' ⟨b, hb⟩
    refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
    · have := congrArg Subtype.val hi
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
      simp only [Prod.pow_fst, Prod.fst_one, pow_add, pow_mul, this, one_pow]
    · have := congrArg Subtype.val hj
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
      simp only [Prod.pow_snd, Prod.snd_one, pow_add, mul_comm (p ^ i), pow_mul, this, one_pow]
  have hidx : ¬ p ∣ T₀.index := by
    rw [index_prod]
    exact (Fact.out : p.Prime).not_dvd_mul T₁.not_dvd_index T₂.not_dvd_index
  let T : Sylow p (G₁ × G₂) := hT₀.toSylow hidx
  let E := E₁.prodMap E₂
  have hE : Function.Injective E := Prod.map_injective.2 ⟨hE₁, hE₂⟩
  refine (realizable_iff p F).2 ⟨G₁ × G₂, inferInstance, inferInstance, T, E, hE, ?_, ?_⟩
  · rw [MonoidHom.range_prodMap, hr₁, hr₂]; rfl
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

/-- The "only if" half, in the generality the proof gives: if `F = F₁ × F₂` over finite
2-groups is realizable and has no nontrivial normal subgroup, then `F₁` and `F₂` are realizable. -/
theorem realizable_factors [GoldschmidtTheoremA] {S₁ : Type u} {S₂ : Type v} [Group S₁]
    [Group S₂] (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)}
    {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} (hprod : IsProduct F F₁ F₂)
    (hO : ∀ D : Subgroup (S₁ × S₂), F.IsNormalSubgroup D → D = ⊥) (h : Realizable 2 F) :
    Realizable 2 F₁ ∧ Realizable 2 F₂ := by
  have hS := isPGroup_prod h₁ h₂
  obtain ⟨G, _, _, T, E, hE, hr, hR⟩ := (realizable_iff 2 F).1 h
  obtain ⟨T', hE', hr', hR'⟩ := realizedBy_quotient_oddCore hS T hE hr hR
  have hodd := goldschmidtOddCore_quotient_eq_bot (G := G)
  exact ⟨realizable_fst_of_oddCore_eq_bot hS hprod.isProdVia hR' hE' T' hr' hodd hO,
    realizable_fst_of_oddCore_eq_bot hS hprod.isProdVia.swap hR' hE' T' hr' hodd hO⟩

/-- **AOV Theorem 3.8, realizability clause.** Let `F` be a reduced fusion system over the 2-group
`S = S₁ × S₂` with `F = F₁ × F₂`, `Fᵢ` a fusion system over `Sᵢ`. Then `F` is realizable if and
only if `F₁` and `F₂` are both realizable. -/
theorem theorem_3_8_realizable [GoldschmidtTheoremA] {S₁ : Type u} {S₂ : Type v} [Group S₁]
    [Group S₂] [Finite S₁] [Finite S₂] (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂)
    (F : FusionSystem (S₁ × S₂)) (F₁ : FusionSystem S₁) (F₂ : FusionSystem S₂)
    (hred : F.Reduced 2) (hprod : IsProduct F F₁ F₂) :
    Realizable 2 F ↔ Realizable 2 F₁ ∧ Realizable 2 F₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨realizable_factors h₁ h₂ hprod hred.2.1, fun h => realizable_product hprod h.1 h.2⟩

end AndersenOliverVentura
