import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Suzuki group `Suz`

The corpus theorem bounding the TauCeti presented group `Suz`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.Suz

/-- The corpus bound on the order of the presented group `Suz`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Suz.Group` is finite of order at most
  `448345497600`.
  Corpus: `CFSG.Sporadic.Presentation.Suz.finite_card_le`,
  CFSG/Sporadic/Presentation/Suz.lean:9. -/
  finite_card_le :
    Finite TauCeti.SporadicName.Suz.Group ∧
    Nat.card TauCeti.SporadicName.Suz.Group ≤ 448345497600

end CFSGOutside.Corpus.Suz
