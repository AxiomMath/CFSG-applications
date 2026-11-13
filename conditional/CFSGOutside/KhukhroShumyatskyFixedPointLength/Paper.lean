import CFSGOutside.KhukhroShumyatskyFixedPointLength.Main

/-!
# Khukhro–Shumyatsky, nonsoluble length and fixed points (fast path)

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), no. 9, 3781–3790, arXiv:1405.1946.

* `CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_coprime_action` and
  `nonsolubleLengthLE_of_coprime_action` (Theorem 1.3), in `Main`;
* `nonsolubleLength_le_of_commSub_eq_top` and `nonsolubleLengthLE_of_commSub_eq_top` (Proposition 3.2), in
  `Chain` and `Main`;
* `nonsolubleLength_le_of_prime` and `nonsolubleLengthLE_of_prime` (the prime case of Theorem 1.3), in `Main`.

Each takes the classification statement `TauCeti.ClassificationStatement` as in the paper, and the corpus theorems
`OddOrder` (Feit–Thompson) and `Schreier` as class hypotheses where it uses them.
-/
