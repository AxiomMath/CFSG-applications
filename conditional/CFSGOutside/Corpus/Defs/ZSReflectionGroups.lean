import Mathlib

/-!
# Copied corpus definitions: the Zalesskiĭ–Serežkin reflection-group families

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that a build importing the corpus too sees no clash:

* `ggCoxeterMatrixD` from `CFSG/LocalAnalysis/StandardType/GGCoxeterLabelCLLDType.lean`;
* `GGIsWeylMatrix` from `CFSG/LocalAnalysis/StandardType/GGOneFiveDefs.lean`;
* `piMat`, `aMat`, `herRefl`, `om` (with the local instance `factPrimeThirteen`) from
  `CFSG/LocalAnalysis/StandardType/GGSecFiveZSMatrices.lean`;
* `IsRefl`, `ReflGen`, `AbsIrred`, `LinWeyl`, `IsIsom`, `ClassRefl`, `permMap`, `diagMap`, `pairUnit`,
  `gmmn`, `g2mmn`, `DMax`, `OneClass`, `ExcRow` and its fields, `n4Gens`, `en4Gens`, `ctRoots`, `k6Gens`,
  `k5Gens`, `glClosure`, `IsReflMat`, `mdeg`, `model`, `ModelIso`, `Family` and `UseInput` from
  `CFSG/LocalAnalysis/StandardType/GGSecFiveZSInputs.lean` (lines 12–175).
-/

noncomputable section

namespace CFSGOutside.Corpus.StandardType

def ggCoxeterMatrixD (n : ℕ) : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j => if i = j then 1 else if CartanMatrix.D n i j = 0 then 2 else 3
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, (CartanMatrix.D_isSymm n).apply j i,
      eq_comm (a := j)]
  diagonal i := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

def GGIsWeylMatrix {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ (M = (CoxeterMatrix.A n).reindex e ∨
      (2 ≤ n ∧ M = (CoxeterMatrix.B n).reindex e) ∨
      (4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e))) ∨
    (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
    (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
    (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e) ∨
    (∃ e : Fin 4 ≃ ι, M = CoxeterMatrix.F₄.reindex e) ∨
    (∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e)

namespace ZS

local instance factPrimeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

def piMat {n : ℕ} (i j : Fin n) (α : ZMod 13) : Matrix (Fin n) (Fin n) (ZMod 13) :=
  fun r c => if r = i ∧ c = j then α else if r = j ∧ c = i then α⁻¹
    else if r = c ∧ r ≠ i ∧ r ≠ j then 1 else 0

def aMat : Matrix (Fin 4) (Fin 4) (ZMod 13) :=
  fun r c => (if r = c then 1 else 0) - 7

def herRefl {n : ℕ} (v vb : Fin n → ZMod 13) : Matrix (Fin n) (Fin n) (ZMod 13) :=
  1 - (2 / (∑ i, v i * vb i)) • Matrix.of fun r c => v r * vb c

def om : ZMod 13 := 3

open Subgroup

section Linear

def IsRefl (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (t : U ≃ₗ[ZMod p] U) : Prop :=
  t * t = 1 ∧
    Module.finrank (ZMod p) (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)) = 1

def ReflGen (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  A = closure {t | t ∈ A ∧ IsRefl p t}

def AbsIrred (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  (∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    ∀ T : Module.End (ZMod p) U,
      (∀ a ∈ A, T ∘ₗ (a : U →ₗ[ZMod p] U) = (a : U →ₗ[ZMod p] U) ∘ₗ T) →
        ∃ c : ZMod p, T = c • LinearMap.id

def LinWeyl (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M ∧
    ∃ f : M.Group ≃* ↥A, ∀ i, IsRefl p (f (M.simple i) : U ≃ₗ[ZMod p] U)

def IsIsom (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (g : U ≃ₗ[ZMod p] U) : Prop := ∀ v, Q (g v) = Q v

def ClassRefl (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (c : ZMod p) : Set (U ≃ₗ[ZMod p] U) :=
  {t | IsRefl p t ∧ IsIsom p Q t ∧ ∃ a, Q a = c ∧ t a = -a}

def permMap (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n)) :
    U ≃ₗ[ZMod p] U :=
  f.equiv f σ

def diagMap (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) : U ≃ₗ[ZMod p] U :=
  f.equivFun.trans ((LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (d i)).trans
    f.equivFun.symm)

def pairUnit (p : ℕ) {n : ℕ} (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) : Fin n → (ZMod p)ˣ :=
  fun i => if i = i₀ then ζ else if i = i₁ then ζ⁻¹ else 1

def gmmn (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  closure (Set.range (permMap p f) ∪ {diagMap p f (pairUnit p i₀ i₁ ζ)})

def g2mmn (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  closure (Set.range (permMap p f) ∪
    {diagMap p f (fun i => if i = i₀ then -1 else 1), diagMap p f (pairUnit p i₀ i₁ ζ)})

def DMax (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) (d : ℕ) : Prop :=
  (∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ d) ∧
    ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = d

def OneClass (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → ∃ g ∈ A, y = g * x * g⁻¹

end Linear

inductive ExcRow
  | N4 | EN4 | K5 | K6 | H4 | H3 | J34 | J35 | EJ35 | J44
  deriving DecidableEq

namespace ExcRow

def deg : ExcRow → ℕ
  | N4 | EN4 | H4 | J44 => 4 | K5 => 5 | K6 => 6 | H3 | J34 | J35 | EJ35 => 3

def ord : ExcRow → ℕ
  | N4 => 2 ^ 9 * 3 * 5 | EN4 => 2 ^ 10 * 3 ^ 2 * 5 | K5 => 2 ^ 7 * 3 ^ 4 * 5
  | K6 => 2 ^ 9 * 3 ^ 7 * 5 * 7 | H4 => 2 ^ 6 * 3 ^ 2 * 5 ^ 2 | H3 => 120 | J34 => 336
  | J35 => 2 ^ 4 * 3 ^ 3 * 5 | EJ35 => 2 ^ 5 * 3 ^ 3 * 5 * 7 | J44 => 2 ^ 9 * 3 ^ 2 * 5 * 7

def cen : ExcRow → ℕ
  | N4 | EN4 | J44 => 4 | K5 | H4 | H3 | J34 => 2 | K6 | J35 | EJ35 => 6

def dmax : ExcRow → ℕ
  | N4 | EN4 | J34 | J44 => 4 | K5 | K6 => 3 | H4 | H3 | J35 | EJ35 => 5

def admissible (p : ℕ) : ExcRow → Prop
  | N4 | EN4 => True | K5 | K6 => p ≠ 3 | H4 | H3 => p ≠ 5 | J34 => p ≠ 7 | J35 => p ≠ 3
  | EJ35 => p = 5 | J44 => p = 3

def needsModel : ExcRow → Prop
  | N4 | EN4 | K5 | K6 => True | _ => False

end ExcRow

section Models

attribute [local instance] factPrimeThirteen

def n4Gens : Set (Matrix (Fin 4) (Fin 4) (ZMod 13)) :=
  {piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat}

def en4Gens : Set (Matrix (Fin 4) (Fin 4) (ZMod 13)) :=
  n4Gens ∪ {Matrix.diagonal fun i => if i = 3 then -1 else 1}

def ctRoots : Set ((Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) :=
  {w | ∃ i j : Fin 6, i < j ∧ ∃ k : ℕ, k < 3 ∧
      w = (Pi.single i 1 - Pi.single j (om ^ k), Pi.single i 1 - Pi.single j (om ^ (2 * k)))} ∪
  {w | ∃ t : Fin 6 → ℕ, t 0 = 0 ∧ (∀ i, t i < 3) ∧ (∑ i, t i) % 3 = 0 ∧
      w = (fun i => om ^ t i, fun i => om ^ (2 * t i))}

def k6Gens : Set (Matrix (Fin 6) (Fin 6) (ZMod 13)) :=
  {M | ∃ w ∈ ctRoots, M = herRefl w.1 w.2}

def k5Gens : Set (Matrix (Fin 6) (Fin 6) (ZMod 13)) :=
  {M | ∃ w ∈ ctRoots, (w.1 0 - w.1 1 = 0) ∧ M = herRefl w.1 w.2}

def glClosure {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) (ZMod 13))) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) :=
  closure {g | (g : Matrix (Fin n) (Fin n) (ZMod 13)) ∈ S}

def IsReflMat {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 13)) : Prop :=
  g * g = 1 ∧ ((g : Matrix (Fin n) (Fin n) (ZMod 13)) - 1).rank = 1

def mdeg : ExcRow → ℕ
  | .K5 => 6 | k => k.deg

def model : (k : ExcRow) → Subgroup (Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13))
  | .N4 => glClosure n4Gens | .EN4 => glClosure en4Gens
  | .K5 => glClosure k5Gens | .K6 => glClosure k6Gens
  | _ => ⊥

def ModelIso (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (k : ExcRow) (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ f : ↥(model k) ≃* ↥A, ∀ g : ↥(model k), IsReflMat g.1 ↔
    IsRefl p (f g : U ≃ₗ[ZMod p] U)

end Models


section UseForm

inductive Family (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop
  | weyl : LinWeyl p A → Family p A
  | slpm : (∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) →
      Family p A
  | orth (Q : QuadraticForm (ZMod p) U) : (QuadraticMap.polarBilin Q).Nondegenerate →
      (∀ g, g ∈ A ↔ IsIsom p Q g) → Family p A
  | orthClass (Q : QuadraticForm (ZMod p) U) (c : ZMod p) :
      (QuadraticMap.polarBilin Q).Nondegenerate → c ≠ 0 → A = closure (ClassRefl p Q c) → Family p A
  | gmmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) (m : ℕ) :
      i₀ ≠ i₁ → 3 ≤ m → orderOf ζ = m → A = gmmn p f i₀ i₁ ζ → Family p A
  | g2mmn {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) (m : ℕ) :
      i₀ ≠ i₁ → 2 ≤ m → orderOf ζ = 2 * m → A = g2mmn p f i₀ i₁ ζ → Family p A
  | exc (k : ExcRow) : k.admissible p → Module.finrank (ZMod p) U = k.deg →
      Nat.card A = k.ord → Nat.card (center A) = k.cen → DMax p A k.dmax → OneClass p A →
      (k.needsModel → ModelIso p k A) → Family p A
  | h4 : p ≠ 5 → Module.finrank (ZMod p) U = 4 → Nat.card A = 14400 →
      (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ A → DMax p A 5 → OneClass p A → Family p A

def UseInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (U : Type) [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (A : Subgroup (U ≃ₗ[ZMod p] U)), p ≠ 2 →
      3 ≤ Module.finrank (ZMod p) U → ReflGen p A → AbsIrred p A → Family p A

end UseForm

end ZS

end CFSGOutside.Corpus.StandardType
