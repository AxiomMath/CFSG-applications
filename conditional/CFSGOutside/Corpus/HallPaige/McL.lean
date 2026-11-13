import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the McLaughlin group

The corpus theorem bounding the TauCeti presented group `McL`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.McL

/-- The corpus bound on the order of the presented group `McL`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.McL.Group` is finite of order at most
  `898128000`.
  Corpus: `CFSG.Sporadic.Presentation.McL.finite_card_le`,
  CFSG/Sporadic/Presentation/McLExact.lean:10. -/
  finite_card_le :
    Finite TauCeti.SporadicName.McL.Group ∧
    Nat.card TauCeti.SporadicName.McL.Group ≤ 898128000

end CFSGOutside.Corpus.McL
