import CFSGOutside.HerzogK3Groups.Paper
import CFSGOutsideClean.Corpus.CfsgClassification
import CFSGOutsideClean.Corpus.LieOrderBridgeHolds
import CFSGOutsideClean.Corpus.SL2MinimalFaithfulZsigmondy
import CFSGOutsideClean.Corpus.SporadicOrdersTableHolds

/-! Herzog (1968): the simple groups with exactly three prime divisors, in order form and in catalogue form,
with the classification, the Lie and sporadic order tables and Zsigmondy's theorem supplied by the corpus. -/

/-- **Herzog (1968).** A nonabelian finite simple group whose order has exactly three prime divisors has one of
the orders 60, 168, 360, 504, 2448, 5616, 6048, 25920.

Source: M. Herzog, On finite simple groups of order divisible by three primes only, J. Algebra 10 (1968), 383–388. -/
theorem CFSGOutsideClean.HerzogK3Groups.herzog_orders (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    Nat.card G ∈ CFSGOutside.HerzogK3Groups.herzogOrders :=
  CFSGOutside.HerzogK3Groups.herzog_orders G hnonab h3

/-- **Herzog (1968), isomorphism form.** A nonabelian finite simple group whose order has exactly three prime
divisors is isomorphic to `A₅`, `A₆`, `PSL(2,7)`, `PSL(2,8)`, `PSL(2,17)`, `PSL(3,3)`, `PSU(3,3)` or `PSU(4,2)`, given as
the catalogue groups in `HerzogCatalog`.

Source: M. Herzog, On finite simple groups of order divisible by three primes only, J. Algebra 10 (1968), 383–388. -/
theorem CFSGOutsideClean.HerzogK3Groups.herzog_iso (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h3 : (Nat.card G).primeFactors.card = 3) :
    ∃ i : TauCeti.CFSGIndex, CFSGOutside.HerzogK3Groups.HerzogCatalog i ∧ Nonempty (G ≃* i.Group) :=
  CFSGOutside.HerzogK3Groups.herzog_iso G hnonab h3
