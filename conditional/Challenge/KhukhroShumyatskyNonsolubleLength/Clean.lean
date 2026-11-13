import CFSGOutside.KhukhroShumyatskyNonsolubleLength.Statement

/-!
# Khukhro–Shumyatsky, Theorem 1.1 and Corollary 1.2

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*, Israel J. Math. **207**
(2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434. (a) The nonsoluble length of a finite group is at most
`2 L₂ + 1`, `L₂` the maximum `2`-length of its soluble subgroups; Corollary 1.2 bounds it by the maximum Fitting
height of soluble subgroups. (b) For an odd prime `p`, the non-`p`-soluble length is at most the maximum
`p`-length of `p`-soluble subgroups. Unconditional: the classification of finite simple groups and the corpus
theorems are not hypotheses.
-/

section

open Subgroup CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyNonsolubleLength

theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ 2 * paperMaxTwoLength G + 1 := sorry

theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a_series
    (G : Type) [Group G] [Finite G] (l : ℕ)
    (h : ∀ H : Subgroup G, Group.IsSolvable H →
      ∃ s : PaperSeries H TwoOrOdd, s.count OddOrderFactor ≤ l) :
    ∃ s : PaperSeries G SolOrSemisimple, s.count SolubleFactor ≤ 2 * l + 1 := sorry

theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.corollary_1_2
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ maxFittingHeight G := sorry

theorem CFSGOutsideClean.KhukhroShumyatskyNonsolubleLength.theorem_1_1_b
    {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (G : Type) [Group G] [Finite G] :
    CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperNonPSolubleLength p G ≤
      CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperMaxPLength p G := sorry

end
