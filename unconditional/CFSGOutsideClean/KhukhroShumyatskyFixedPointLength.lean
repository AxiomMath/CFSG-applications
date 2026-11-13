import Comparator.Solution
import CFSGOutside.KhukhroShumyatskyFixedPointLength.Paper
import CFSGOutsideClean.Corpus.OddOrder
import CFSGOutsideClean.Corpus.Schreier

/-!
# Khukhro–Shumyatsky, Theorem 1.3 and Proposition 3.2 (clean path)

E. I. Khukhro and P. Shumyatsky, *On the length of finite groups and of fixed points*, Proc. Amer. Math. Soc.
**143** (2015), no. 9, 3781–3790, arXiv:1405.1946. The classification statement is supplied by the corpus,
`CFSGComparator.classification`, and Feit–Thompson and the Schreier conjecture for the catalogue by the
instances in `CFSGOutsideClean.Corpus`. No hypothesis beyond the paper's own remains.
-/

section

open CFSGOutside.NonsolubleLength ArithmeticFunction
open CFSGOutside.KhukhroShumyatskyFixedPointLength (fixA fixedSub commSub)

/-- **Theorem 1.3 (Khukhro–Shumyatsky, Proc. AMS 2015)**, explicit-bound form: if a finite group `A` acts on a
finite group `G` by automorphisms with `(|A|, |G|) = 1` and `λ(C_G(A)) ≤ l`, then
`λ(G) ≤ 2^{α(|A|)} (l + 1) - 1`, where `α(n) = Ω(n)` counts the prime factors of `n` with multiplicity. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_coprime_action
    {G A : Type} [Group G] [Finite G] [Group A] [Finite A] (α : A →* MulAut G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) {l : ℕ}
    (hl : NonsolubleLengthLE (fixA α) l) :
    NonsolubleLengthLE G (2 ^ cardFactors (Nat.card A) * (l + 1) - 1) :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_coprime_action
    CFSGComparator.classification.{0} α hcop hl

/-- **Length and fixed points.** If a finite group A acts by automorphisms on a finite group G of coprime order, then
λ(G) ≤ 2^α(|A|)·(λ(C_G(A)) + 1) − 1, where λ is nonsoluble length and α(n) is the number of prime factors of n
counted with multiplicity. If φ is an automorphism of G of prime order p not dividing |G|, then λ(G) ≤ 2λ(C_G(φ)) +
1, and λ(G) ≤ λ(C_G(φ)) + 1 when G = [G, φ].

Source: E. I. Khukhro and P. Shumyatsky, On the length of finite groups and of fixed points, Proc. Amer. Math. Soc.
143 (2015), 3781–3790, Theorem 1.3 and Proposition 3.2. https://arxiv.org/abs/1405.1946 -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_coprime_action
    {G A : Type} [Group G] [Finite G] [Group A] [Finite A] (α : A →* MulAut G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    nonsolubleLength G ≤ 2 ^ cardFactors (Nat.card A) * (nonsolubleLength (fixA α) + 1) - 1 :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_coprime_action
    CFSGComparator.classification.{0} α hcop

/-- **Proposition 3.2 (Khukhro–Shumyatsky, Proc. AMS 2015)**, explicit-bound form: if `φ` is an automorphism of
a finite group `G` with `φ ^ p = 1`, `p` a prime not dividing `|G|`, and `G = [G, φ]`, then
`λ(C_G(φ)) ≤ l` gives `λ(G) ≤ l + 1`. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_commSub_eq_top
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) (hcomm : commSub φ = ⊤) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (l + 1) :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_commSub_eq_top
    CFSGComparator.classification.{0} hφ hpG hcomm hl

/-- **Proposition 3.2 (Khukhro–Shumyatsky, Proc. AMS 2015)**: if `φ` is an automorphism of a finite group `G`
with `φ ^ p = 1`, `p` a prime not dividing `|G|`, and `G = [G, φ]`, then `λ(G) ≤ λ(C_G(φ)) + 1`. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_commSub_eq_top
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) (hcomm : commSub φ = ⊤) :
    nonsolubleLength G ≤ nonsolubleLength (fixedSub φ) + 1 :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_commSub_eq_top
    CFSGComparator.classification.{0} hφ hpG hcomm

/-- **The prime case of Theorem 1.3 (Khukhro–Shumyatsky, Proc. AMS 2015)**, explicit-bound form: for `φ` as in
Proposition 3.2 (without `G = [G, φ]`), `λ(C_G(φ)) ≤ l` gives `λ(G) ≤ 2 l + 1`. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_prime
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) {l : ℕ}
    (hl : NonsolubleLengthLE (fixedSub φ) l) : NonsolubleLengthLE G (2 * l + 1) :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLengthLE_of_prime
    CFSGComparator.classification.{0} hφ hpG hl

/-- **The prime case of Theorem 1.3 (Khukhro–Shumyatsky, Proc. AMS 2015)**: for `φ` as in Proposition 3.2
(without `G = [G, φ]`), `λ(G) ≤ 2 λ(C_G(φ)) + 1`. -/
theorem CFSGOutsideClean.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_prime
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {φ : MulAut G}
    (hφ : φ ^ p = 1) (hpG : ¬ p ∣ Nat.card G) :
    nonsolubleLength G ≤ 2 * nonsolubleLength (fixedSub φ) + 1 :=
  CFSGOutside.KhukhroShumyatskyFixedPointLength.nonsolubleLength_le_of_prime
    CFSGComparator.classification.{0} hφ hpG

end
