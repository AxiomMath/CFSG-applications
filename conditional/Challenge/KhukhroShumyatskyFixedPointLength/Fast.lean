import CFSGOutside.KhukhroShumyatskyFixedPointLength.Definitions
import CFSGOutside.Common.NonsolubleLength
import CFSGOutside.Corpus.OddOrder
import CFSGOutside.Corpus.Schreier

/-!
# Khukhro–Shumyatsky, Theorem 1.3 and Proposition 3.2 (fast version)

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), no. 9, 3781–3790, arXiv:1405.1946. If a finite group `A` acts on a finite group `G` by
automorphisms with `(|A|, |G|) = 1`, then `λ(G) ≤ 2^{α(|A|)} (λ(C_G(A)) + 1) - 1` (Theorem 1.3), where `α(n)` is
the number of prime factors of `n` with multiplicity; if `φ` has prime order `p ∤ |G|` and `G = [G, φ]`, then
`λ(G) ≤ λ(C_G(φ)) + 1` (Proposition 3.2); and `λ(G) ≤ 2 λ(C_G(φ)) + 1` without `G = [G, φ]` (the prime case of
Theorem 1.3). The classification of finite simple groups is a hypothesis, as in the paper. The corpus theorems the proofs use
are class hypotheses: `OddOrder` (Feit–Thompson) and `Schreier`.
-/

section

open CFSGOutside.NonsolubleLength CFSGOutside.KhukhroShumyatskyFixedPointLength ArithmeticFunction

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_coprime_action
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {G A : Type} [Group G] [Finite G] [Group A] [Finite A] (α : A →* MulAut G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) {l : ℕ}
    (hl : NonsolubleLengthLE (fixA α) l) :
    NonsolubleLengthLE G (2 ^ cardFactors (Nat.card A) * (l + 1) - 1) := sorry

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_coprime_action
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {G A : Type} [Group G] [Finite G] [Group A] [Finite A] (α : A →* MulAut G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    nonsolubleLength G ≤ 2 ^ cardFactors (Nat.card A) * (nonsolubleLength (fixA α) + 1) - 1 := sorry

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_commSub_eq_top
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) (hcomm : commSub φ = ⊤) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (l + 1) := sorry

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_commSub_eq_top
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) (hcomm : commSub φ = ⊤) :
    nonsolubleLength G ≤ nonsolubleLength (fixedSub φ) + 1 := sorry

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_prime
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (2 * l + 1) := sorry

theorem CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_prime
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Schreier] (hCFSG : TauCeti.ClassificationStatement.{0}) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) :
    nonsolubleLength G ≤ 2 * nonsolubleLength (fixedSub φ) + 1 := sorry

end
