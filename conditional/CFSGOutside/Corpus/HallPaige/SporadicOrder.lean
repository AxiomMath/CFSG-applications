import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Corpus input: order bounds for sporadic presented groups

Upper bounds for the orders of TauCeti presented sporadic groups, proved in the corpus by coset
enumeration, stated as classes whose fields are the corpus statements from AxiomMath/CFSG @ 69cb972. They
are used by the sporadic-group certificates (`results_conditional/CFSGOutside/HallPaige/Sporadic/*.lean`) to see that explicit
words generate a whole point stabilizer.
-/

namespace CFSGOutside.Corpus

/-- The corpus bounds on the orders of the presented groups `J₃` and `He`. -/
class Bounds : Prop where
  /-- **`|J₃| ≤ 50232960`** for the TauCeti presentation of `J₃`.
  Corpus: `CFSG.Sporadic.Presentation.J3.finite_card_le`, CFSG/Sporadic/Presentation/J3.lean:43
  (AxiomMath/CFSG @ 69cb972). -/
  j3_finite_card_le : Finite TauCeti.SporadicName.J3.Group ∧
    Nat.card TauCeti.SporadicName.J3.Group ≤ 50232960
  /-- **`|He| ≤ 4030387200`** for the TauCeti presentation of the Held group.
  Corpus: `CFSG.Sporadic.Presentation.He.finite_card_le`, CFSG/Sporadic/Presentation/HeExact.lean:9
  (AxiomMath/CFSG @ 69cb972). -/
  he_finite_card_le : Finite TauCeti.SporadicName.He.Group ∧
    Nat.card TauCeti.SporadicName.He.Group ≤ 4030387200

end CFSGOutside.Corpus
