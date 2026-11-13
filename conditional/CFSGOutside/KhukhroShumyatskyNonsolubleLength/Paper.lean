import CFSGOutside.KhukhroShumyatskyNonsolubleLength.TheoremA
import CFSGOutside.KhukhroShumyatskyNonsolubleLength.TheoremB

/-!
# Khukhro–Shumyatsky, nonsoluble and non-`p`-soluble length (fast path)

E. I. Khukhro and P. Shumyatsky, *Nonsoluble and non-p-soluble length of finite groups*, Israel J. Math. **207**
(2015), DOI 10.1007/s11856-015-1180-x, arXiv:1310.2434.

* `CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_a`, `theorem_1_1_a_series` (Theorem 1.1(a)) and
  `corollary_1_2` (Corollary 1.2), in `TheoremA`;
* `CFSGOutside.KhukhroShumyatskyNonsolubleLength.theorem_1_1_b` (Theorem 1.1(b)), in `TheoremB`.

Each takes the classification statement `TauCeti.ClassificationStatement` as in the paper, and the corpus
theorems it uses as classes: `OddOrder` and `Schreier` for (a), `ThompsonElementaryNormalPComplement` and
`Schreier` for (b).
-/
