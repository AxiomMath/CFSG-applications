import CFSGOutside.AndersenOliverVentura.Defs
import CFSGOutside.Corpus.GoldschmidtTheoremA

/-!
# Andersen–Oliver–Ventura, Theorem 3.8, realizability clause (fast path)

K. K. S. Andersen, B. Oliver, J. Ventura, *Reduced, tame and exotic fusion systems*, Proc. London
Math. Soc. (3) 105 (2012), 87–152, DOI 10.1112/plms/pdr065; Theorem 3.8 of arXiv:1009.0622.
Only the realizability clause; the tame and strongly tame clauses are not formalized.
The definitions are in `CFSGOutside.AndersenOliverVentura.Defs`.
Conditional on Goldschmidt's Theorem A, `CFSGOutside.Corpus.GoldschmidtTheoremA`.
-/

open CFSGOutside.Corpus AndersenOliverVentura

universe u v

theorem AndersenOliverVentura.realizable_product {p : ℕ} [Fact p.Prime] {S₁ : Type u} {S₂ : Type v}
    [Group S₁] [Group S₂] {F : FusionSystem (S₁ × S₂)} {F₁ : FusionSystem S₁}
    {F₂ : FusionSystem S₂} (hprod : IsProduct F F₁ F₂) (h₁ : Realizable p F₁)
    (h₂ : Realizable p F₂) : Realizable p F := sorry

theorem AndersenOliverVentura.realizable_factors [GoldschmidtTheoremA] {S₁ : Type u} {S₂ : Type v}
    [Group S₁] [Group S₂] (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)}
    {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} (hprod : IsProduct F F₁ F₂)
    (hO : ∀ D : Subgroup (S₁ × S₂), F.IsNormalSubgroup D → D = ⊥) (h : Realizable 2 F) :
    Realizable 2 F₁ ∧ Realizable 2 F₂ := sorry

theorem AndersenOliverVentura.theorem_3_8_realizable [GoldschmidtTheoremA] {S₁ : Type u}
    {S₂ : Type v} [Group S₁] [Group S₂] [Finite S₁] [Finite S₂] (h₁ : IsPGroup 2 S₁)
    (h₂ : IsPGroup 2 S₂) (F : FusionSystem (S₁ × S₂)) (F₁ : FusionSystem S₁)
    (F₂ : FusionSystem S₂) (hred : F.Reduced 2) (hprod : IsProduct F F₁ F₂) :
    Realizable 2 F ↔ Realizable 2 F₁ ∧ Realizable 2 F₂ := sorry
