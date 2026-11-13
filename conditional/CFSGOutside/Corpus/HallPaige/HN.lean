import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Harada–Norton group

The corpus theorem bounding the TauCeti presented group `HN`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.HN

/-- The corpus bound on the order of the presented group `HN`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.HN.Group` is finite of order at most `273030912000000`.
  Corpus: `CFSG.Sporadic.Presentation.HN.finite_card_le`, CFSG/Sporadic/Presentation/HN.lean:10. -/
  finite_card_le :
    Finite TauCeti.SporadicName.HN.Group ∧
    Nat.card TauCeti.SporadicName.HN.Group ≤ 273030912000000

end CFSGOutside.Corpus.HN
