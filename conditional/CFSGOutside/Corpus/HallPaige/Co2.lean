import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the second Conway group

The corpus theorem bounding the TauCeti presented group `Co2`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.Co2

/-- The corpus bound on the order of the presented group `Co₂`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Co2.Group` is finite of order at most
  `42305421312000`.
  Corpus: `CFSG.Sporadic.Presentation.Co2.finite_card_le`,
  CFSG/Sporadic/Presentation/Co2.lean:9. -/
  finite_card_le :
    Finite TauCeti.SporadicName.Co2.Group ∧
    Nat.card TauCeti.SporadicName.Co2.Group ≤ 42305421312000

end CFSGOutside.Corpus.Co2
