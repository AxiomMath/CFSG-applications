import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the O'Nan group

The corpus theorem bounding the TauCeti presented group `ONan`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.ONan

/-- The corpus bound on the order of the presented group `O'N`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.ONan.Group` is finite of order at most `460815505920`.
  Corpus: `CFSG.Sporadic.Presentation.ONan.finite_card_le`, CFSG/Sporadic/Presentation/ONan.lean:17. -/
  finite_card_le :
    Finite TauCeti.SporadicName.ONan.Group ∧
    Nat.card TauCeti.SporadicName.ONan.Group ≤ 460815505920

end CFSGOutside.Corpus.ONan
