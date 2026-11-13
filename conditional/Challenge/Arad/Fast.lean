import CFSGOutside.Arad.Defs
import CFSGOutside.Corpus.WalterStructure
import CFSGOutside.Corpus.J2Inverted
import CFSGOutside.Corpus.WardLocal
import CFSGOutside.Corpus.GorensteinWalter
import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime

/-!
# Arad, Theorem B(iii) (fast path)

Z. Arad, *π-homogeneity and π′-closure of finite groups*, Pacific J. Math. 51 (1974), 1–9, Theorem B(iii).
Conditional on the corpus theorems stated as classes in `CFSGOutside.Corpus`. The notions `IsPiHomogeneous`,
`IsPiPrimeClosed` and `SylowTwoDihedralOrAbelian` are in `CFSGOutside.Arad.Defs`.
-/

namespace CFSGOutside.Arad

open CFSGOutside.Corpus

/-- **Theorem B(iii)** (Arad, Pacific J. Math. 51 (1974), p. 2): *Let `π` be a set of odd primes. Then `G` is
π′-closed if `G` is π-homogeneous and `G` has dihedral or abelian Sylow `2`-subgroups.* -/
theorem theorem_B_iii [WalterStructure] [J2Inverted] [WardOrder] [WardTwoThree] [WardFour]
    [GorensteinWalter] [ExistsIsSylowOfNormalizedOfCoprime.{0}] {π : Set ℕ}
    (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G)
    (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G := sorry

end CFSGOutside.Arad
