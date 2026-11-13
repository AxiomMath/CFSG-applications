import CFSGOutside.KhukhroShumyatskyNonsolubleLength.Statement
import CFSGOutside.Corpus.OddOrder
import CFSGOutside.Corpus.Schreier
import CFSGOutside.Corpus.ThompsonElementaryNormalPComplement

/-!
# Khukhro–Shumyatsky, Theorem 1.1 and Corollary 1.2 (fast path)

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*, Israel J. Math. **207**
(2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434. (a) The nonsoluble length of a finite group is at most
`2 L₂ + 1`, `L₂` the maximum `2`-length of its soluble subgroups; Corollary 1.2 bounds it by the maximum Fitting
height of soluble subgroups. (b) For an odd prime `p`, the non-`p`-soluble length is at most the maximum
`p`-length of `p`-soluble subgroups. The classification of finite simple groups is a hypothesis, as in the
paper. The corpus theorems the proofs use are class
hypotheses: `OddOrder` and `Schreier` for (a), `ThompsonElementaryNormalPComplement` and `Schreier` for (b).
-/

section

open Subgroup CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyNonsolubleLength

theorem CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ 2 * paperMaxTwoLength G + 1 := sorry

theorem CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a_series
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    (G : Type) [Group G] [Finite G] (l : ℕ)
    (h : ∀ H : Subgroup G, Group.IsSolvable H →
      ∃ s : PaperSeries H TwoOrOdd, s.count OddOrderFactor ≤ l) :
    ∃ s : PaperSeries G SolOrSemisimple, s.count SolubleFactor ≤ 2 * l + 1 := sorry

theorem CFSGOutside.KhukhroShumyatskyNonsolubleLength.corollary_1_2
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    (G : Type) [Group G] [Finite G] : paperNonsolubleLength G ≤ maxFittingHeight G := sorry

theorem CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_b
    {p : ℕ} [hp : Fact p.Prime]
    [CFSGOutside.Corpus.ThompsonElementaryNormalPComplement.{0}] [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    (hp2 : p ≠ 2) (G : Type) [Group G] [Finite G] :
    CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperNonPSolubleLength p G ≤
      CFSGOutside.KhukhroShumyatskyNonsolubleLength.paperMaxPLength p G := sorry

end
