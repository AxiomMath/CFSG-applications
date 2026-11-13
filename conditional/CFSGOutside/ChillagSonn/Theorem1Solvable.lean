import CFSGOutside.ChillagSonn.Lemma14
import CFSGOutside.ChillagSonn.SylowTower

/-!
# Theorem 1, case (i): solvable Sylow-metacyclic groups

By Lemma (1.4), `G = NA` with `N ⊴ G` of order prime to 6 and `A` a Hall subgroup of order `2ᵃ3ᵇ`; `N` is a
Sylow-metacyclic group of odd order, so it has a Sylow tower.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus

/-- **Chillag–Sonn, Theorem 1, solvable case.** A finite solvable Sylow-metacyclic group satisfies case (i) of
Theorem 1. -/
theorem theorem_1_solvable [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [SolvableHallExistence.{0}] [SolvableHallConjugacy.{0}] {G : Type}
    [Group G] [Finite G] (hG : SylowMetacyclic G) (hs : Group.IsSolvable G) : Theorem1Conclusion G := by
  obtain ⟨N, A, hNn, hinf, hsup, hcop, hA, hAhall⟩ := lemma_1_4 (hG 2) (hG 3)
  have hodd : Odd (Nat.card N) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hcop)
  exact ⟨N, A, hNn, hinf, hsup, hodd, hasSylowTower_of_odd (hG.subgroup N) hodd,
    Or.inl ⟨hs, hA, hAhall, hcop⟩⟩

end CFSGOutside.ChillagSonn
