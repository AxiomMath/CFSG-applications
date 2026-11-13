import CFSGOutside.Corpus.Defs.OpenVocabulary
import CFSGOutside.Corpus.Defs.ZSReflectionGroups

/-!
# Copied corpus definitions: automorphisms of `B*` and the Weyl-group inputs of §5

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus`:

* `ggInduced`, `GGIsReflection`, `GGIsTransvection`, `GGNoTransvection` from
  `CFSG/LocalAnalysis/StandardType/GGOneFiveDefs.lean` (lines 53–129);
* `GGSecFiveRootReflInput` from `CFSG/LocalAnalysis/StandardType/GGSecFiveJoinPrimed.lean` (line 362);
* `GGSecFiveCoxProdInput` from `CFSG/LocalAnalysis/StandardType/GGSecFiveCoxProd.lean` (line 9).

`IsElemAbelian` is the copy `CFSGOutside.Corpus.Open.IsElemAbelian` of `CFSG.Open.IsElemAbelian`.
-/

namespace CFSGOutside.Corpus.StandardType

open CFSGOutside.Corpus.Open

section Defs

variable {G : Type} [Group G] [Finite G]

def ggInduced (H Bs : Subgroup G) : Set (MulAut ↥Bs) :=
  {φ | ∃ g ∈ H, g ∈ Subgroup.normalizer (Bs : Set G) ∧
    ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹}

def GGIsReflection (p : ℕ) {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  φ ^ 2 = 1 ∧ Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs

def GGIsTransvection (p : ℕ) {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs ∧ ∀ b : ↥Bs, φ (b⁻¹ * φ b) = b⁻¹ * φ b

def GGNoTransvection (p : ℕ) (Bs : Subgroup G) : Prop :=
  ∀ φ ∈ ggInduced ⊤ Bs, ¬ GGIsTransvection p φ

end Defs

def GGSecFiveRootReflInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → GGNoTransvection p Bs →
      ∀ (A : Subgroup (MulAut ↥Bs)), A ≤ ggInduced ⊤ Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
          (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
          ∀ f : M.Group ≃* ↥A, (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) →
            ∀ a : ↥A, GGIsReflection p (a : MulAut ↥Bs) →
              ∃ (i : ι) (g : M.Group), a = f (g * M.simple i * g⁻¹)

def GGSecFiveCoxProdInput : Prop :=
  ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
    (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
      ∀ (i j : ι) (g h : M.Group),
        orderOf (g * M.simple i * g⁻¹ * (h * M.simple j * h⁻¹)) ≤ 4

end CFSGOutside.Corpus.StandardType
