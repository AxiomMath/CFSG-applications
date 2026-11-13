import CFSGOutside.Arad.Reduction
import CFSGOutside.Arad.Simple
import CFSGOutside.Arad.Dihedral
import CFSGOutside.Arad.Abelian

/-!
# Arad, Theorem B(iii)

Z. Arad, *π-homogeneity and π′-closure of finite groups*, Pacific J. Math. 51 (1974), 1–9, Theorem B(iii)
(statement p. 2, proof p. 7). Conditional on the corpus theorems stated as the classes `WalterStructure`,
`J2Inverted`, `WardOrder`, `WardTwoThree`, `WardFour`, `GorensteinWalter` and
`ExistsIsSylowOfNormalizedOfCoprime` in `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Arad

open CFSGOutside.Corpus

/-- **π-homogeneous groups.** Let π be a set of odd primes and G a finite group in which, for every nonidentity
π-subgroup H, the group N_G(H)/C_G(H) is a π-group. If every Sylow 2-subgroup of G is abelian or dihedral, then the
elements of G whose orders are divisible by no prime of π form a subgroup.

Source: Z. Arad, π-homogeneity and π′-closure of finite groups, Pacific J. Math. 51 (1974), 1–9, Theorem B(iii).
https://doi.org/10.2140/pjm.1974.51.1

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_B_iii' [WalterStructure] [J2Inverted] [WardOrder] [WardTwoThree] [WardFour]
    [GorensteinWalter] [ExistsIsSylowOfNormalizedOfCoprime.{0}] {π : Set ℕ} (h2 : 2 ∉ π)
    {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G) (hS : SylowTwoDihedralOrAbelian G) :
    IsPiPrimeClosed π G := by
  obtain ⟨K, hK⟩ := exists_isNormalPiPrimeHall (π := π)
    (fun (G : Type) [Group G] => SylowTwoDihedralOrAbelian G)
    (fun _ _ _ H h => sylowTwoDihedralOrAbelian_subgroup h H)
    (fun _ _ _ N _ h => sylowTwoDihedralOrAbelian_quotient h N)
    (fun G _ _ _ hnonab hS hH => not_dvd_card_of_isSimpleGroup h2 G hnonab hS hH)
    G hS (homP_of_isPiHomogeneous hG)
  exact isPiPrimeClosed_of_isNormalPiPrimeHall hK

/-- **Theorem B(iii)** (Arad, Pacific J. Math. 51 (1974), p. 2): *Let `π` be a set of odd primes. Then `G` is
π′-closed if `G` is π-homogeneous and `G` has dihedral or abelian Sylow `2`-subgroups.* -/
theorem theorem_B_iii [WalterStructure] [J2Inverted] [WardOrder] [WardTwoThree] [WardFour]
    [GorensteinWalter] [ExistsIsSylowOfNormalizedOfCoprime.{0}] {π : Set ℕ}
    (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G)
    (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G :=
  theorem_B_iii' (fun h => (Nat.not_even_iff_odd.mpr (hπ 2 h).2) even_two) hG hS

/-- **Theorem B(iii), abelian case** (Arad, Pacific J. Math. 51 (1974), p. 2), a special case of
`theorem_B_iii` that needs Walter's theorem but not the Gorenstein–Walter theorem: *let `π` be a set of odd primes;
if `G` is π-homogeneous and has abelian Sylow `2`-subgroups, then `G` is π′-closed.* -/
theorem theorem_B_iii_abelian [WalterStructure] [J2Inverted] [WardOrder] [WardTwoThree] [WardFour]
    [ExistsIsSylowOfNormalizedOfCoprime.{0}] {π : Set ℕ} (hπ : ∀ p ∈ π, p.Prime ∧ Odd p)
    {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G)
    (hS : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) : IsPiPrimeClosed π G := by
  have h2 : 2 ∉ π := fun h => (Nat.not_even_iff_odd.mpr (hπ 2 h).2) even_two
  obtain ⟨K, hK⟩ := exists_isNormalPiPrimeHall (π := π)
    (fun (G : Type) [Group G] => SylowTwoAbelian G)
    (fun _ _ _ H h => sylowTwoAbelian_subgroup h H)
    (fun _ _ _ N _ h => sylowTwoAbelian_quotient h N)
    (fun G _ _ _ hnonab hS hH => not_dvd_card_of_isSimpleGroup_abelian h2 G hnonab hS hH)
    G hS (homP_of_isPiHomogeneous hG)
  exact isPiPrimeClosed_of_isNormalPiPrimeHall hK

end CFSGOutside.Arad
