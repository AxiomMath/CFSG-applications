import CFSGOutside.Corpus.Defs.ReeModel
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Copied corpus definitions: order formulas of the finite simple groups of Lie type

Definitions copied verbatim from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The copies are:

* `Open.orderA` to `Open.orderTits` from `CFSG/Open/OrderForm.lean` (lines 12 to 64);
* `HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula` from
  `CFSG/HardMathSupport/Solomon/Coordinator/I14_20LieOrd.lean` (line 362), the order of the catalogue group of a
  Lie type index;
* `ComponentClassification.CatLeaf.lieOrderNumerator`, `lieOrderDivisor` and `lieSylowExponent` from
  `CFSG/LocalAnalysis/ComponentClassification/CatLeafInputs.lean` (lines 26, 52 and 64), indexed by the copy of
  `StatedLieTag` in `CFSGOutside.Corpus.Defs.ReeModel`.

`clean/CFSGOutsideClean/Corpus/Defs/LieOrder.lean` shows that each copy equals its original.
-/

namespace CFSGOutside.Corpus

namespace Open

open Finset

/-- Order of `PSL_{n+1}(q)`; `CFSG.Open.orderA`, `OrderForm.lean` line 12. -/
def orderA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Icc 2 (n + 1), (q ^ i - 1)) / Nat.gcd (n + 1) (q - 1)

/-- Order of `PSU_{n+1}(q)`; `CFSG.Open.orderTwistedA`, `OrderForm.lean` line 15. -/
def orderTwistedA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Icc 2 (n + 1), if Even i then q ^ i - 1 else q ^ i + 1) /
    Nat.gcd (n + 1) (q + 1)

/-- Order of `PSp_{2n}(q)` and of `PΩ_{2n+1}(q)`; `CFSG.Open.orderBC`, `OrderForm.lean` line 19. -/
def orderBC (n q : ℕ) : ℕ :=
  q ^ (n * n) * (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) / Nat.gcd 2 (q - 1)

/-- Order of `PΩ⁺_{2n}(q)`; `CFSG.Open.orderD`, `OrderForm.lean` line 22. -/
def orderD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n - 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n - 1)

/-- Order of `PΩ⁻_{2n}(q)`; `CFSG.Open.orderTwistedD`, `OrderForm.lean` line 26. -/
def orderTwistedD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n + 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n + 1)

/-- Order of `E₆(q)`; `CFSG.Open.orderE6`, `OrderForm.lean` line 30. -/
def orderE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q - 1)

/-- Order of `²E₆(q)`; `CFSG.Open.orderTwistedE6`, `OrderForm.lean` line 34. -/
def orderTwistedE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q + 1)

/-- Order of `E₇(q)`; `CFSG.Open.orderE7`, `OrderForm.lean` line 38. -/
def orderE7 (q : ℕ) : ℕ :=
  q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1) / Nat.gcd 2 (q - 1)

/-- Order of `E₈(q)`; `CFSG.Open.orderE8`, `OrderForm.lean` line 42. -/
def orderE8 (q : ℕ) : ℕ :=
  q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
    (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)

/-- Order of `F₄(q)`; `CFSG.Open.orderF4`, `OrderForm.lean` line 46. -/
def orderF4 (q : ℕ) : ℕ :=
  q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Order of `G₂(q)`; `CFSG.Open.orderG2`, `OrderForm.lean` line 49. -/
def orderG2 (q : ℕ) : ℕ :=
  q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Order of `³D₄(q)`; `CFSG.Open.orderTrialityD4`, `OrderForm.lean` line 52. -/
def orderTrialityD4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Order of the Suzuki group `²B₂(q)`; `CFSG.Open.orderSuzuki`, `OrderForm.lean` line 55. -/
def orderSuzuki (q : ℕ) : ℕ :=
  q ^ 2 * (q ^ 2 + 1) * (q - 1)

/-- Order of the Ree group `²G₂(q)`; `CFSG.Open.orderRee`, `OrderForm.lean` line 58. -/
def orderRee (q : ℕ) : ℕ :=
  q ^ 3 * (q ^ 3 + 1) * (q - 1)

/-- Order of the Ree group `²F₄(q)`; `CFSG.Open.orderTwistedF4`, `OrderForm.lean` line 61. -/
def orderTwistedF4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)

/-- Order of the Tits group `²F₄(2)′`; `CFSG.Open.orderTits`, `OrderForm.lean` line 64. -/
def orderTits : ℕ := 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13

end Open

namespace HardMathSupport.Solomon.Coordinator.I1420

open Open

/-- Corpus `CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula`: the order of the catalogue
group of a Lie type index. -/
def lieOrderFormula : TauCeti.LieTypeIndex → ℕ
  | .A n q => orderA n q.card
  | .twistedA n q => orderTwistedA n q.card
  | .B n q => orderBC n q.card
  | .C n q => orderBC n q.card
  | .D n q => orderD n q.card
  | .twistedD n q => orderTwistedD n q.card
  | .E6 q => orderE6 q.card
  | .E7 q => orderE7 q.card
  | .E8 q => orderE8 q.card
  | .F4 q => orderF4 q.card
  | .G2 q => orderG2 q.card
  | .twistedE6 q => orderTwistedE6 q.card
  | .trialityD4 q => orderTrialityD4 q.card
  | .suzuki m => orderSuzuki (2 ^ (2 * m + 1))
  | .reeG2 m => orderRee (3 ^ (2 * m + 1))
  | .reeF4 m => orderTwistedF4 (2 ^ (2 * m + 1))
  | .tits => orderTits

end HardMathSupport.Solomon.Coordinator.I1420

namespace ComponentClassification.CatLeaf

open Open

/-- The numerator `q ^ N * C` of the order formula of the group of type `t` over a field with `q`
elements, `CFSG.ComponentClassification.CatLeaf.lieOrderNumerator`, `CatLeafInputs.lean` line 26. -/
def lieOrderNumerator : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)
  | .PSU, n, q => q ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)
  | .PSp, n, q => q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaOdd, n, q => q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaPlus, n, q => q ^ (n * (n - 1)) * (q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .POmegaMinus, n, q => q ^ (n * (n - 1)) * (q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .G2, _, q => q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .F4, _, q => q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E6, _, q => q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)
  | .E7, _, q => q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E8, _, q => q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) *
      (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
  | .twistedE6, _, q => q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)
  | .trialityD4, _, q => q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .twistedB2, _, q => q ^ 2 * (q ^ 2 + 1) * (q - 1)
  | .twistedG2, _, q => q ^ 3 * (q ^ 3 + 1) * (q - 1)
  | .twistedF4, _, q => q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
  | .Tits, _, _ => 17971200

/-- The divisor `D` by which the numerator is divided, `CFSG.ComponentClassification.CatLeaf.lieOrderDivisor`,
`CatLeafInputs.lean` line 52. -/
def lieOrderDivisor : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => Nat.gcd n (q - 1)
  | .PSU, n, q => Nat.gcd n (q + 1)
  | .PSp, _, q => Nat.gcd 2 (q - 1)
  | .POmegaOdd, _, _ => 2
  | .POmegaPlus, n, q => Nat.gcd 4 (q ^ n - 1)
  | .POmegaMinus, n, q => Nat.gcd 4 (q ^ n + 1)
  | .E6, _, q => Nat.gcd 3 (q - 1)
  | .E7, _, q => Nat.gcd 2 (q - 1)
  | .twistedE6, _, q => Nat.gcd 3 (q + 1)
  | _, _, _ => 1

/-- The exponent `N` of the `p`-part `q ^ N` of the order, `CFSG.ComponentClassification.CatLeaf.lieSylowExponent`,
`CatLeafInputs.lean` line 64. -/
def lieSylowExponent : StatedLieTag → ℕ → ℕ
  | .PSL, n => n * (n - 1) / 2
  | .PSU, n => n * (n - 1) / 2
  | .PSp, n => n ^ 2
  | .POmegaOdd, n => n ^ 2
  | .POmegaPlus, n => n * (n - 1)
  | .POmegaMinus, n => n * (n - 1)
  | .G2, _ => 6
  | .F4, _ => 24
  | .E6, _ => 36
  | .E7, _ => 63
  | .E8, _ => 120
  | .twistedE6, _ => 36
  | .trialityD4, _ => 12
  | .twistedB2, _ => 2
  | .twistedG2, _ => 3
  | .twistedF4, _ => 12
  | .Tits, _ => 11

end ComponentClassification.CatLeaf

end CFSGOutside.Corpus
