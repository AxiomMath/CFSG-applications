import Mathlib
import CFSGOutside.HerzogK3Groups.Defs
import CFSGOutside.Corpus.CfsgClassification
import CFSGOutside.Corpus.LieOrderBridgeHolds
import CFSGOutside.Corpus.SporadicOrdersTableHolds
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy

/-!
# Herzog, simple groups of order divisible by three primes only (fast path)

M. Herzog, J. Algebra 10 (1968), 383–388. Conditional on the corpus inputs stated as classes in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.HerzogK3Groups

open CFSGOutside.Corpus

variable [SL2MinimalFaithfulZsigmondy]

/-- **Herzog (1968).** A nonabelian finite simple group whose order has exactly three prime divisors has one of
the orders 60, 168, 360, 504, 2448, 5616, 6048, 25920.

Source: M. Herzog, On finite simple groups of order divisible by three primes only, J. Algebra 10 (1968), 383–388. -/
theorem herzog_orders [CfsgClassification] [LieOrderBridgeHolds] [SporadicOrdersTableHolds]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    Nat.card G ∈ herzogOrders :=
  sorry

/-- **Herzog (1968), isomorphism form.** A nonabelian finite simple group whose order has exactly three prime
divisors is isomorphic to `A₅`, `A₆`, `PSL(2,7)`, `PSL(2,8)`, `PSL(2,17)`, `PSL(3,3)`, `PSU(3,3)` or `PSU(4,2)`, given as
the catalogue groups in `HerzogCatalog`.

Source: M. Herzog, On finite simple groups of order divisible by three primes only, J. Algebra 10 (1968), 383–388. -/
theorem herzog_iso [CfsgClassification] [LieOrderBridgeHolds] [SporadicOrdersTableHolds]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    ∃ i : TauCeti.CFSGIndex, HerzogCatalog i ∧ Nonempty (G ≃* i.Group) :=
  sorry

end CFSGOutside.HerzogK3Groups
