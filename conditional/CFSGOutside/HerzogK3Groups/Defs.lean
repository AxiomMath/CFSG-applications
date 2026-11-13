import Mathlib
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-! The orders and catalogue indices of Herzog's simple K3-groups, kept apart from the proof so that the challenge
statements can import them. -/

namespace CFSGOutside.HerzogK3Groups

/-- The orders of the eight simple K3-groups. -/
def herzogOrders : Finset ℕ := {60, 168, 360, 504, 2448, 5616, 6048, 25920}

/-- The catalog parameters at which a Lie-type group has exactly three prime divisors. -/
def HerzogLie : TauCeti.LieTypeIndex → Prop
  | .A 1 q => q.card = 4 ∨ q.card = 5 ∨ q.card = 7 ∨ q.card = 8 ∨ q.card = 9 ∨ q.card = 17
  | .A 2 q => q.card = 2 ∨ q.card = 3
  | .twistedA 2 q => q.card = 3
  | .twistedA 3 q => q.card = 2
  | .B 2 q => q.card = 3
  | _ => False

/-- The catalog indices of the groups in Herzog's theorem: A5, A6 and the parameter sets of `HerzogLie`. -/
def HerzogCatalog : TauCeti.CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => n = 5 ∨ n = 6
  | .lie idx => HerzogLie idx.1
  | .sporadic _ => False

end CFSGOutside.HerzogK3Groups
