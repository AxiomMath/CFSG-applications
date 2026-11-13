import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import CFSGOutside.Corpus.Defs.ZSReflectionGroups

/-! The definitions copied into `CFSGOutside.Corpus.Defs.ZSReflectionGroups` are the corpus definitions.

The plain definitions agree by `rfl`. `ExcRow` and `Family` are inductive copies, so `family_of_corpus` maps a corpus
`Family` proof to a copied one constructor by constructor, sending each exceptional row to the copied row of the
same name. -/

namespace CFSGOutsideClean.Corpus.StandardType

open CFSGOutside.Corpus.StandardType in
theorem ggCoxeterMatrixD_eq (n : ℕ) : ggCoxeterMatrixD n = CFSG.StandardType.ggCoxeterMatrixD n :=
  rfl

theorem ggIsWeylMatrix_iff {ι : Type} (M : CoxeterMatrix ι) :
    CFSGOutside.Corpus.StandardType.GGIsWeylMatrix M ↔ CFSG.StandardType.GGIsWeylMatrix M :=
  Iff.rfl

namespace ZS

variable (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isRefl_iff (t : U ≃ₗ[ZMod p] U) :
    CFSGOutside.Corpus.StandardType.ZS.IsRefl p t ↔ CFSG.StandardType.ZS.IsRefl p t :=
  Iff.rfl

theorem reflGen_iff (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    CFSGOutside.Corpus.StandardType.ZS.ReflGen p A ↔ CFSG.StandardType.ZS.ReflGen p A :=
  Iff.rfl

theorem absIrred_iff (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    CFSGOutside.Corpus.StandardType.ZS.AbsIrred p A ↔ CFSG.StandardType.ZS.AbsIrred p A :=
  Iff.rfl

theorem linWeyl_iff (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    CFSGOutside.Corpus.StandardType.ZS.LinWeyl p A ↔ CFSG.StandardType.ZS.LinWeyl p A :=
  Iff.rfl

theorem gmmn_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    CFSGOutside.Corpus.StandardType.ZS.gmmn p f i₀ i₁ ζ = CFSG.StandardType.ZS.gmmn p f i₀ i₁ ζ :=
  rfl

theorem g2mmn_eq {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    CFSGOutside.Corpus.StandardType.ZS.g2mmn p f i₀ i₁ ζ = CFSG.StandardType.ZS.g2mmn p f i₀ i₁ ζ :=
  rfl

theorem classRefl_eq (Q : QuadraticForm (ZMod p) U) (c : ZMod p) :
    CFSGOutside.Corpus.StandardType.ZS.ClassRefl p Q c = CFSG.StandardType.ZS.ClassRefl p Q c :=
  rfl

theorem family_of_corpus {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : CFSG.StandardType.ZS.Family p A) : CFSGOutside.Corpus.StandardType.ZS.Family p A := by
  cases h with
  | weyl h => exact .weyl h
  | slpm h => exact .slpm h
  | orth Q hQ h => exact .orth Q hQ h
  | orthClass Q c hQ hc h => exact .orthClass Q c hQ hc h
  | gmmn f i₀ i₁ ζ m h₀ h₁ h₂ h₃ => exact .gmmn f i₀ i₁ ζ m h₀ h₁ h₂ h₃
  | g2mmn f i₀ i₁ ζ m h₀ h₁ h₂ h₃ => exact .g2mmn f i₀ i₁ ζ m h₀ h₁ h₂ h₃
  | exc k hk hd ho hc hD hO hM =>
    cases k with
    | N4 => exact .exc .N4 hk hd ho hc hD hO hM
    | EN4 => exact .exc .EN4 hk hd ho hc hD hO hM
    | K5 => exact .exc .K5 hk hd ho hc hD hO hM
    | K6 => exact .exc .K6 hk hd ho hc hD hO hM
    | H4 => exact .exc .H4 hk hd ho hc hD hO hM
    | H3 => exact .exc .H3 hk hd ho hc hD hO hM
    | J34 => exact .exc .J34 hk hd ho hc hD hO hM
    | J35 => exact .exc .J35 hk hd ho hc hD hO hM
    | EJ35 => exact .exc .EJ35 hk hd ho hc hD hO hM
    | J44 => exact .exc .J44 hk hd ho hc hD hO hM
  | h4 h₀ h₁ h₂ h₃ h₄ h₅ => exact .h4 h₀ h₁ h₂ h₃ h₄ h₅

end ZS

theorem useInput_of_corpus (h : CFSG.StandardType.ZS.UseInput) :
    CFSGOutside.Corpus.StandardType.ZS.UseInput :=
  fun p _ U _ _ _ A hp hd hR hA => ZS.family_of_corpus p (h p U A hp hd hR hA)

end CFSGOutsideClean.Corpus.StandardType
