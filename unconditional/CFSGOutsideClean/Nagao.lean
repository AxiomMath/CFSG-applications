import Comparator.Solution
import CFSGOutside.Nagao.SevenTransitive
import CFSGOutsideClean.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix
import CFSGOutsideClean.Corpus.FixedDegreeCases
import CFSGOutsideClean.Corpus.SubgroupCardClassificationOfCardLeEighty
import CFSGOutsideClean.Corpus.Schreier

/-! Nagao (1966), Theorem 3, and its unconditional corollaries for `k ≥ 7`, with the 5-transitive inputs and
Schreier's conjecture supplied by the corpus. `Outer` is the copy of
`CFSG.ComponentClassification.OuterAutomorphisms.Outer`, equal to it by
`CFSGOutsideClean.Corpus.ComponentClassification.OuterAutomorphisms.inner_eq`. -/

open CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

/-- **7-transitive permutation groups.** Let G be a k-transitive permutation group on a finite set Ω with k ≤ |Ω|, such
that every simple subgroup of G has soluble outer automorphism group. If G is neither the symmetric nor the
alternating group on Ω, then k ≤ 6. Consequently every k-transitive group of degree n with 7 ≤ k ≤ n contains the
alternating group.

Source: H. Nagao, On multiply transitive groups I, Nagoya Math. J. 27 (1966), 15–19, Theorem 3.
https://doi.org/10.1017/S0027763000011818 -/
theorem CFSGOutsideClean.Nagao.nagao_theorem3 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω))
    {k : ℕ} (hk : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k)
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → Group.IsSolvable (Outer T))
    (hSym : G ≠ ⊤) (hAlt : G ≠ alternatingGroup Ω) : k ≤ 6 :=
  CFSGOutside.Nagao.nagao_theorem3 G hk hG hOut hSym hAlt

/-- **Corollary of Theorem 3 (Nagao, 1966).** A 7-transitive group of degree `n ≥ 7` contains the
alternating group. Unconditional: the classification statement is supplied by the corpus. -/
theorem CFSGOutsideClean.Nagao.nagao_seven_transitive
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hn : 7 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 7) :
    alternatingGroup Ω ≤ G :=
  CFSGOutside.Nagao.nagao_seven_transitive
    CFSGComparator.classification.{0} G hn hG

/-- **Corollary of Theorem 3 (Nagao, 1966).** A `k`-transitive group of degree `n ≥ k ≥ 7` contains the
alternating group. Unconditional: the classification statement is supplied by the corpus. -/
theorem CFSGOutsideClean.Nagao.nagao_k_transitive
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) {k : ℕ} (hk : 7 ≤ k)
    (hn : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k) :
    alternatingGroup Ω ≤ G :=
  CFSGOutside.Nagao.nagao_k_transitive
    CFSGComparator.classification.{0} G hk hn hG
