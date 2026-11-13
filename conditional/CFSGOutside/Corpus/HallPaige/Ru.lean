import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Rudvalis group

The corpus theorem bounding the TauCeti presented group `Ru`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.Ru

/-- The corpus bound on the order of the presented group `Ru`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Ru.Group` is finite of order at most
  `145926144000`.
  Corpus: `CFSG.Sporadic.Presentation.Ru.finite_card_le`,
  CFSG/Sporadic/Presentation/RuExact.lean:10. -/
  finite_card_le :
    Finite TauCeti.SporadicName.Ru.Group ∧
    Nat.card TauCeti.SporadicName.Ru.Group ≤ 145926144000

end CFSGOutside.Corpus.Ru
