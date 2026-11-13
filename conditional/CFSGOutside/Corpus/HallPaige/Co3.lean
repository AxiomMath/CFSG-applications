import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the third Conway group

The corpus theorem bounding the TauCeti presented group `Co3`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.Co3

/-- The corpus bound on the order of the presented group `Co₃`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Co3.Group` is finite of order at most
  `495766656000`.
  Corpus: `CFSG.Sporadic.Presentation.Co3.finite_card_le`,
  CFSG/Sporadic/Presentation/Co3.lean:10. -/
  finite_card_le :
    Finite TauCeti.SporadicName.Co3.Group ∧
    Nat.card TauCeti.SporadicName.Co3.Group ≤ 495766656000

end CFSGOutside.Corpus.Co3
