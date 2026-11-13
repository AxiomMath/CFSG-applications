import CFSGOutside.Arad.Paper
import CFSGOutsideClean.Corpus.WalterStructure
import CFSGOutsideClean.Corpus.J2Inverted
import CFSGOutsideClean.Corpus.WardLocal
import CFSGOutsideClean.Corpus.GorensteinWalter
import CFSGOutsideClean.Corpus.ExistsIsSylowOfNormalizedOfCoprime

/-! Arad, Theorem B(iii), with Walter's theorem, the properties of `J₁`, Ward's results on groups of Ree type, the
Gorenstein–Walter theorem and the coprime-action Sylow lemma supplied by the corpus. -/

namespace CFSGOutsideClean.Arad

open CFSGOutside.Arad

/-- **π-homogeneous groups.** Let π be a set of odd primes and G a finite group in which, for every nonidentity
π-subgroup H, the group N_G(H)/C_G(H) is a π-group. If every Sylow 2-subgroup of G is abelian or dihedral, then the
elements of G whose orders are divisible by no prime of π form a subgroup.

Source: Z. Arad, π-homogeneity and π′-closure of finite groups, Pacific J. Math. 51 (1974), 1–9, Theorem B(iii).
https://doi.org/10.2140/pjm.1974.51.1 -/
theorem theorem_B_iii {π : Set ℕ} (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G]
    (hG : IsPiHomogeneous π G) (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G :=
  CFSGOutside.Arad.theorem_B_iii hπ hG hS

/-- **Arad 1974, Theorem B(iii)**, for any set `π` of numbers not containing `2`. -/
theorem theorem_B_iii' {π : Set ℕ} (h2 : 2 ∉ π) {G : Type} [Group G] [Finite G] (hG : IsPiHomogeneous π G)
    (hS : SylowTwoDihedralOrAbelian G) : IsPiPrimeClosed π G :=
  CFSGOutside.Arad.theorem_B_iii' h2 hG hS

/-- **Arad 1974, Theorem B(iii), abelian case.** -/
theorem theorem_B_iii_abelian {π : Set ℕ} (hπ : ∀ p ∈ π, p.Prime ∧ Odd p) {G : Type} [Group G] [Finite G]
    (hG : IsPiHomogeneous π G) (hS : ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)) :
    IsPiPrimeClosed π G :=
  CFSGOutside.Arad.theorem_B_iii_abelian hπ hG hS

end CFSGOutsideClean.Arad
