import CFSGOutside.AndersenOliverVentura.Paper
import CFSGOutside.AOVTame.StrongIf
import CFSGOutsideClean.Corpus.GoldschmidtTheoremA
import CFSGOutsideClean.Corpus.AlperinFusion

/-! Andersen–Oliver–Ventura, Theorem 3.8, all three clauses (realizable, tame, strongly tame), with
Goldschmidt's Theorem A (`CFSG.Goldschmidt75.theoremA`) and Alperin's fusion theorem
(`CFSG.RankTwoShapes.alperin_centric_radical_fusion`) supplied by the corpus. -/

namespace CFSGOutsideClean.AndersenOliverVentura

open _root_.AndersenOliverVentura

universe u v

theorem realizable_product {p : ℕ} [Fact p.Prime] {S₁ : Type u} {S₂ : Type v}
    [Group S₁] [Group S₂] {F : FusionSystem (S₁ × S₂)} {F₁ : FusionSystem S₁}
    {F₂ : FusionSystem S₂} (hprod : IsProduct F F₁ F₂) (h₁ : Realizable p F₁)
    (h₂ : Realizable p F₂) : Realizable p F :=
  _root_.AndersenOliverVentura.realizable_product hprod h₁ h₂

theorem realizable_factors {S₁ : Type u} {S₂ : Type v}
    [Group S₁] [Group S₂] (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)}
    {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂} (hprod : IsProduct F F₁ F₂)
    (hO : ∀ D : Subgroup (S₁ × S₂), F.IsNormalSubgroup D → D = ⊥) (h : Realizable 2 F) :
    Realizable 2 F₁ ∧ Realizable 2 F₂ :=
  _root_.AndersenOliverVentura.realizable_factors h₁ h₂ hprod hO h

theorem theorem_3_8_realizable {S₁ : Type u}
    {S₂ : Type v} [Group S₁] [Group S₂] [Finite S₁] [Finite S₂] (h₁ : IsPGroup 2 S₁)
    (h₂ : IsPGroup 2 S₂) (F : FusionSystem (S₁ × S₂)) (F₁ : FusionSystem S₁)
    (F₂ : FusionSystem S₂) (hred : F.Reduced 2) (hprod : IsProduct F F₁ F₂) :
    Realizable 2 F ↔ Realizable 2 F₁ ∧ Realizable 2 F₂ :=
  _root_.AndersenOliverVentura.theorem_3_8_realizable h₁ h₂ F F₁ F₂ hred hprod

end CFSGOutsideClean.AndersenOliverVentura

namespace CFSGOutsideClean.AndersenOliverVentura.Tame

open _root_.AndersenOliverVentura _root_.AndersenOliverVentura.Tame

variable {S₁ S₂ : Type} [Group S₁] [Group S₂] {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}

/-- **Tame fusion systems.** Let F = F₁ × F₂ be a reduced fusion system over S₁ × S₂, where F₁ and F₂ are fusion systems
over finite 2-groups S₁ and S₂. Then F is realizable by a finite group if and only if F₁ and F₂ are, F is tame if
and only if F₁ and F₂ are, and F is strongly tame if and only if F₁ and F₂ are.

Source: K. K. S. Andersen, B. Oliver, J. Ventura, Reduced, tame and exotic fusion systems, Proc. London Math. Soc.
(3) 105 (2012), 87–152, Theorem 3.8. https://doi.org/10.1112/plms/pdr065 -/
theorem theorem_3_8_tame [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) : IsTame 2 F ↔ IsTame 2 F₁ ∧ IsTame 2 F₂ :=
  _root_.AndersenOliverVentura.Tame.theorem_3_8_tame h₁ h₂ hred hprod

/-- **AOV Theorem 3.8, strong tameness clause.** A reduced `F = F₁ × F₂` over a 2-group `S₁ × S₂`
is strongly tame if and only if `F₁` and `F₂` are strongly tame. -/
theorem theorem_3_8_stronglyTame [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) :
    IsStronglyTame 2 F ↔ IsStronglyTame 2 F₁ ∧ IsStronglyTame 2 F₂ :=
  _root_.AndersenOliverVentura.Tame.theorem_3_8_stronglyTame h₁ h₂ hred hprod

end CFSGOutsideClean.AndersenOliverVentura.Tame
