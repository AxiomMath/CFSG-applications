import CFSGOutside.KhukhroShumyatskyFactorizedLength.Statement

/-!
# Khukhro–Shumyatsky, Theorem 1.1 for factorized groups

E. I. Khukhro and P. Shumyatsky, *On the length of finite factorized groups*, Ann. Mat. Pura Appl. (4) **194**
(2015), 1775–1780, DOI 10.1007/s10231-014-0443-1, arXiv:1405.1899. If a finite group `G = AB` is factorized by
two subgroups of coprime orders, then its nonsoluble length is at most `2^{h*(A) + h*(B)} - 1`, `h*` the
generalized Fitting height. No hypotheses beyond the paper's.
-/

section

open CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyFactorizedLength

theorem CFSGOutsideClean.KhukhroShumyatskyFactorizedLength.nonsolubleLengthLE_of_isFactorization
    (G : Type) [Group G] [Finite G] (A B : Subgroup G) (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) {a b : ℕ} (hA : GenFittingHeightLE A a)
    (hB : GenFittingHeightLE B b) : NonsolubleLengthLE G (2 ^ (a + b) - 1) := sorry

theorem CFSGOutsideClean.KhukhroShumyatskyFactorizedLength.nonsolubleLength_le_of_isFactorization
    (G : Type) [Group G] [Finite G] (A B : Subgroup G) (hAB : IsFactorization A B)
    (hcop : (Nat.card A).Coprime (Nat.card B)) :
    nonsolubleLength G ≤ 2 ^ (genFittingHeight A + genFittingHeight B) - 1 := sorry

end
