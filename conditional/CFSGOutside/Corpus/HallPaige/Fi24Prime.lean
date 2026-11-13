import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

/-!
# Corpus input for the Fischer group Fi₂₄'

The corpus theorem bounding the TauCeti presented group `Fi24Prime` by its exact order, stated as a class with
its exact signature.
-/

namespace CFSGOutside.Corpus.Fi24Prime

/-- The corpus bound on the order of the presented group `Fi₂₄'`. -/
class FiniteCardLe : Prop where
  /-- The presented group `TauCeti.SporadicName.Fi24Prime.Group` is finite of order at most
  `1255205709190661721292800`. Corpus: `CFSG.Sporadic.Presentation.Fi24Prime.finite_card_le_exact`,
  CFSG/Sporadic/Presentation/Fi24PrimeExact.lean:19. -/
  finite_card_le_exact :
    Finite TauCeti.SporadicName.Fi24Prime.Group ∧
    Nat.card TauCeti.SporadicName.Fi24Prime.Group ≤ 1255205709190661721292800

end CFSGOutside.Corpus.Fi24Prime
