import Mathlib

/-!
# Corpus input: the Odd Order Theorem

Statement of `CFSG.FeitThompson.isSolvable_of_odd_natCard`, copied verbatim from
`CFSG/FeitThompson/OddOrderTheorem.lean` (line 14) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `CFSG.Milestones.odd_order_solvable` is the same theorem.

The corpus theorem is universe polymorphic, so the class takes the universe as a parameter: a lemma about
`G : Type u` assumes `[OddOrder.{u}]`. The clean build provides every instance, in
`clean/CFSGOutsideClean/Corpus/OddOrder.lean`.
-/

universe u

namespace CFSGOutside.Corpus

/-- Feit–Thompson: a finite group of odd order is solvable. -/
class OddOrder : Prop where
  isSolvable_of_odd_natCard : ∀ (G : Type u) [Group G] [Finite G] (_hG : Odd (Nat.card G)),
    Group.IsSolvable G

end CFSGOutside.Corpus
