import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Fischer group `Fi₂₂`

The corpus theorem bounding the TauCeti presented group `Fi22`, stated as a class with its
exact signature.
-/

namespace CFSGOutside.Corpus.Fi22

/-- The corpus bound on the order of the presented group `Fi₂₂`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Fi22.Group` is finite of order at most
  `64561751654400`.
  Corpus: `CFSG.Sporadic.Presentation.Fi22.finite_card_le`,
  CFSG/Sporadic/Presentation/Fi22Exact.lean:11. -/
  finite_card_le :
    Finite TauCeti.SporadicName.Fi22.Group ∧
    Nat.card TauCeti.SporadicName.Fi22.Group ≤ 64561751654400

end CFSGOutside.Corpus.Fi22
