import CFSGOutside.AOVTame.StrongTame
import CFSGOutside.Corpus.AlperinFusion
import CFSGOutside.Corpus.GoldschmidtTheoremA

/-!
# Andersen–Oliver–Ventura, Theorem 3.8, tameness clauses (fast path)

K. K. S. Andersen, B. Oliver, J. Ventura, *Reduced, tame and exotic fusion systems*, Proc. London
Math. Soc. (3) 105 (2012), 87–152, DOI 10.1112/plms/pdr065; Theorem 3.8 of arXiv:1009.0622: for `p = 2`, a
reduced `F = F₁ × F₂` over `S = S₁ × S₂` is tame, or strongly tame, if and only if `F₁` and `F₂` both are. The
realizability clause is in `Challenge/AndersenOliverVentura/Fast.lean`. The definitions are in
`CFSGOutside.AndersenOliverVentura.Defs`, `CFSGOutside.AOVTame.Defs` and `CFSGOutside.AOVTame.StrongTame`.
Conditional on Goldschmidt's Theorem A and Alperin's fusion theorem, stated as classes in `CFSGOutside.Corpus`.
-/

namespace AndersenOliverVentura.Tame

open CFSGOutside.Corpus

variable {S₁ S₂ : Type} [Group S₁] [Group S₂] {F₁ : FusionSystem S₁} {F₂ : FusionSystem S₂}

theorem theorem_3_8_tame [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) : IsTame 2 F ↔ IsTame 2 F₁ ∧ IsTame 2 F₂ := sorry

theorem theorem_3_8_stronglyTame [GoldschmidtTheoremA] [AlperinFusion] [Finite S₁] [Finite S₂]
    (h₁ : IsPGroup 2 S₁) (h₂ : IsPGroup 2 S₂) {F : FusionSystem (S₁ × S₂)} (hred : F.Reduced 2)
    (hprod : IsProduct F F₁ F₂) :
    IsStronglyTame 2 F ↔ IsStronglyTame 2 F₁ ∧ IsStronglyTame 2 F₂ := sorry

end AndersenOliverVentura.Tame
