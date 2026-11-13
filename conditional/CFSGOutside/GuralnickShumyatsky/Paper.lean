import CFSGOutside.GuralnickShumyatsky.Cor2
import CFSGOutside.GuralnickShumyatsky.Order

/-!
# Guralnick–Shumyatsky, Theorems 3.1 and 3.6 (fast path)

R. Guralnick and P. Shumyatsky, *Derived subgroups of fixed points*, Israel J. Math. 126 (2001), 345–362,
DOI 10.1007/BF02784161. Let `A` be an elementary abelian group of order `q³` acting coprimely on a finite
group `G`. This file collects the headline results, each conditional on the corpus inputs stated as classes
in `CFSGOutside.Corpus`:

* `CFSGOutside.GuralnickShumyatsky.theorem_3_1` (`Main.lean`), Theorem 3.1 = Theorem 1.4: for an
  `A`-invariant Sylow `p`-subgroup `P` of `G`, `P ∩ G' = ⟨P ∩ C_G(a)' | a ∈ A#⟩`;
* `CFSGOutside.GuralnickShumyatsky.theorem_3_6` (`Order.lean`), Theorem 3.6, the explicit form of Theorem 1.1:
  if `|C_G(a)'| ≤ m` for all `a ∈ A#`, then `|G'| ≤ m ^ (2(q² + q + 1))`;
* `corollary_3_3`, `corollary_3_4` (`Cor.lean`) and `corollary_3_5` (`Cor2.lean`): Corollaries 3.3 to 3.5.

Not formalized: Theorems 1.2 and 1.3, which need Zelmanov's Lie ring methods, and Corollary 3.2.
-/
