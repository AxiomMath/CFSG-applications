import Comparator.Solution
import CFSGOutside.KhukhroShumyatskyNonsolubleLength.Paper
import CFSGOutsideClean.Corpus.OddOrder
import CFSGOutsideClean.Corpus.Schreier
import CFSGOutsideClean.Corpus.ThompsonElementaryNormalPComplement

/-!
# Khukhro–Shumyatsky, Theorem 1.1(a), (b) and Corollary 1.2 (clean path)

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*, Israel J. Math. **207**
(2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434. The classification statement is supplied by the corpus,
`CFSGComparator.classification`, and the Odd Order theorem, the Schreier conjecture for the catalogue and
Thompson's normal `p`-complement theorem by the instances in `CFSGOutsideClean.Corpus`.
-/

section

open Subgroup CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyNonsolubleLength

/-- **Nonsoluble length of groups.** Let G be a finite group and λ(G) its nonsoluble length, the least number of
nonsoluble factors in a normal series of G whose factors are soluble or direct products of nonabelian simple groups.
Then λ(G) ≤ 2L₂ + 1, where L₂ is the maximum 2-length of a soluble subgroup of G, and λ(G) is at most the maximum
Fitting height of a soluble subgroup of G. For an odd prime p, the non-p-soluble length of G is at most the maximum
p-length of a p-soluble subgroup of G.

Source: E. I. Khukhro and P. Shumyatsky, Nonsoluble and non-p-soluble length of finite groups, Israel J. Math. 207
(2015), 507–525, Theorem 1.1 and Corollary 1.2. https://doi.org/10.1007/s11856-015-1180-x -/
theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ 2 * paperMaxTwoLength G + 1 :=
  CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a CFSGComparator.classification.{0} G

/-- **Theorem 1.1(a) (Khukhro–Shumyatsky, Israel J. Math. 2015)**, unpacked: if every soluble subgroup of `G`
has a normal series with `2`- and `2'`-factors having at most `l` factors of even order, then `G` has a normal
series with soluble or semisimple factors having at most `2l + 1` nonsoluble factors. Unconditional. -/
theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a_series
    (G : Type) [Group G] [Finite G] (l : ℕ)
    (h : ∀ H : Subgroup G, Group.IsSolvable H →
      ∃ s : PaperSeries H TwoOrOdd, s.count OddOrderFactor ≤ l) :
    ∃ s : PaperSeries G SolOrSemisimple, s.count SolubleFactor ≤ 2 * l + 1 :=
  CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a_series CFSGComparator.classification.{0} G l h

/-- **Corollary 1.2 (Khukhro–Shumyatsky, Israel J. Math. 2015).** The nonsoluble length `λ(G)` of a finite
group `G` does not exceed the maximum Fitting height of soluble subgroups of `G`. Unconditional. -/
theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.corollary_1_2
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ maxFittingHeight G :=
  CFSGOutside.KhukhroShumyatskyNonsolubleLength.corollary_1_2 CFSGComparator.classification.{0} G

/-- **Theorem 1.1(b) (Khukhro–Shumyatsky, Israel J. Math. 2015).** For an odd prime `p`, the non-`p`-soluble
length `λ_p(G)` of a finite group `G` does not exceed the maximum `p`-length of `p`-soluble subgroups of `G`.
Unconditional. -/
theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_b
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (G : Type) [Group G] [Finite G] :
    CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperNonPSolubleLength p G ≤
      CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperMaxPLength p G :=
  CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_b CFSGComparator.classification.{0} hp2 G

end
