import CFSGOutside.Corpus.Defs.OuterAutomorphisms
import CFSGOutside.Corpus.Schreier
import CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix
import CFSGOutside.Corpus.FixedDegreeCases
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-!
# Nagao, Theorem 3 (fast path)

H. Nagao, *On multiply transitive groups I*, Nagoya Math. J. 27 (1966), 15–19,
DOI 10.1017/S0027763000011818. A `k`-transitive group of degree `n` in which every simple subgroup has a
solvable outer automorphism group satisfies `k ≤ 6` unless it is `S_n` or `A_n`. Assuming the classification
statement, every `k`-transitive group of degree `n ≥ k ≥ 7` contains the alternating group.
Conditional on the corpus inputs stated as classes in `CFSGOutside.Corpus`.
-/

open CFSGOutside.Corpus.ComponentClassification.OuterAutomorphisms

theorem CFSGOutside.Nagao.nagao_theorem3
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω))
    {k : ℕ} (hk : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k)
    (hOut : ∀ T : Subgroup G, IsSimpleGroup T → Group.IsSolvable (Outer T))
    (hSym : G ≠ ⊤) (hAlt : G ≠ alternatingGroup Ω) : k ≤ 6 := sorry

theorem CFSGOutside.Nagao.nagao_seven_transitive
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω))
    (hn : 7 ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω 7) :
    alternatingGroup Ω ≤ G := sorry

theorem CFSGOutside.Nagao.nagao_k_transitive
    [CFSGOutside.Corpus.AlternatingGroupLeOfNontrivialSupportLeSix]
    [CFSGOutside.Corpus.FixedDegreeCases]
    [CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty]
    [CFSGOutside.Corpus.Schreier]
    (hCFSG : TauCeti.ClassificationStatement.{0})
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) {k : ℕ} (hk : 7 ≤ k)
    (hn : k ≤ Fintype.card Ω) (hG : MulAction.IsMultiplyPretransitive G Ω k) :
    alternatingGroup Ω ≤ G := sorry
