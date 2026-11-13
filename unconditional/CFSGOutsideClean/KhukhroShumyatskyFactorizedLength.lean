import Comparator.Solution
import CFSGOutside.KhukhroShumyatskyFactorizedLength.Paper
import CFSGOutsideClean.Corpus.BurnsidePQ
import CFSGOutsideClean.Corpus.Schreier

/-!
# Khukhro–Shumyatsky, Theorem 1.1 for factorized groups (clean path)

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780, DOI 10.1007/s10231-014-0443-1, arXiv:1405.1899. The classification statement is supplied by
the corpus, `CFSGComparator.classification`, and the corpus theorems by the instances in
`CFSGOutsideClean.Corpus`.
-/

open CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyFactorizedLength

/-- **Theorem 1.1 (Khukhro–Shumyatsky, Ann. Mat. Pura Appl. 2015)**, in `∀`-form: if `G = AB` with
`gcd(|A|, |B|) = 1`, `h*(A) ≤ a` and `h*(B) ≤ b`, then `λ(G) ≤ 2^{a+b} - 1`. Unconditional: no corpus
hypotheses remain. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFactorizedLength.nonsolubleLengthLE_of_isFactorization
    (G : Type) [Group G] [Finite G] (A B : Subgroup G) (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) {a b : ℕ} (hA : GenFittingHeightLE A a)
    (hB : GenFittingHeightLE B b) : NonsolubleLengthLE G (2 ^ (a + b) - 1) :=
  CFSGOutside.KhukhroShumyatskyFactorizedLength.nonsolubleLengthLE_of_isFactorization
    CFSGComparator.classification.{0} G A B hAB hcop hA hB

/-- **Length of factorized groups.** Let G = AB be a finite group with A and B subgroups of coprime orders. Then the
nonsoluble length of G is at most 2^(h*(A) + h*(B)) − 1, where h*(X) is the generalized Fitting height of X, the
least h with F*_h(X) = X for the series F*_{i+1}(X)/F*_i(X) = F*(X/F*_i(X)).

Source: E. I. Khukhro and P. Shumyatsky, On the length of finite factorized groups, Ann. Mat. Pura Appl. 194 (2015),
1775–1780, Theorem 1.1. https://doi.org/10.1007/s10231-014-0443-1 -/
theorem CFSGOutsideClean.KhukhroShumyatskyFactorizedLength.nonsolubleLength_le_of_isFactorization
    (G : Type) [Group G] [Finite G] (A B : Subgroup G) (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    nonsolubleLength G ≤ 2 ^ (genFittingHeight A + genFittingHeight B) - 1 :=
  CFSGOutside.KhukhroShumyatskyFactorizedLength.nonsolubleLength_le_of_isFactorization
    CFSGComparator.classification.{0} G A B hAB hcop
