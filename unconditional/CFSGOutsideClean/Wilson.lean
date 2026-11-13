import Comparator.Solution
import CFSGOutside.Wilson.Paper
import CFSGOutsideClean.Corpus.Schreier
import CFSGOutsideClean.Corpus.Defs.PSolvable

/-!
# Wilson, Theorem 2\* and Lemma 4(ii) (clean path)

J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66 (EuDML 178137).

The classification statement is supplied by the corpus, `CFSGComparator.classification`, and Schreier's conjecture
for the catalogue by the instance in `CFSGOutsideClean.Corpus.Schreier`. `IsPSolvable` is the copy of
`CFSG.HallHigman.IsPSolvable`, equal to it by `CFSGOutsideClean.Corpus.isPSolvable_eq`.
-/

open Subgroup CFSGOutside.Corpus CFSGOutside.Wilson

/-- **Compact torsion groups.** Let p be a prime, H a finite group, K a normal subgroup of H, Q a Sylow p-subgroup of K,
and t ∈ H with (tq)^(p^a) = 1 for every q ∈ Q. Then K has a series 1 = K₀ ≤ K₁ ≤ ⋯ ≤ K_{2a+1} = K of subgroups
normal in H in which K_{2i+1}/K_{2i} is p-soluble and K_{2i+2}/K_{2i+1} is a direct product of nonabelian simple
groups of order divisible by p. If instead (tq)^(p^(a+1)) = 1 for all q ∈ Q and N is the normal closure in H of the
elements (tq)^(p^a), there are subgroups K₁ ≤ K₂ ≤ K ∩ N, normal in H, with K₁ p-soluble, K₂/K₁ a direct product of
nonabelian simple groups of order divisible by p, and (K ∩ N)/K₂ soluble.

Source: J. S. Wilson, On the structure of compact torsion groups, Monatsh. Math. 96 (1983), 57–66, Theorem 2* and
Lemma 4(ii). https://eudml.org/doc/178137 -/
theorem CFSGOutsideClean.Wilson.wilson_theorem2star {p : ℕ}
    [Fact p.Prime] {H : Type} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    (Q : Sylow p K) (t : H) (a : ℕ) (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ a) = 1) :
    ∃ S : ℕ → Subgroup H, S 0 = ⊥ ∧ S (2 * a + 1) = K ∧ (∀ i, (S i).Normal) ∧
      (∀ i < 2 * a + 1, S i ≤ S (i + 1)) ∧
      (∀ i ≤ a, ∃ _ : ((S (2 * i)).subgroupOf (S (2 * i + 1))).Normal,
        IsPSolvable p (S (2 * i + 1) ⧸ (S (2 * i)).subgroupOf (S (2 * i + 1)))) ∧
      (∀ i < a, ∃ _ : ((S (2 * i + 1)).subgroupOf (S (2 * i + 2))).Normal,
        IsSpProd p (S (2 * i + 2) ⧸ (S (2 * i + 1)).subgroupOf (S (2 * i + 2)))) :=
  CFSGOutside.Wilson.wilson_theorem2star CFSGComparator.classification.{0} K Q t a hexp

/-- **Wilson, Lemma 4(ii)** (Monatsh. Math. 96 (1983), p. 63), with `a + 1` in place of `a`. Let `K ⊴ H`,
`Q ∈ Syl_p(K)` and `t ∈ H` with `(tq)^(p^(a+1)) = 1` for all `q ∈ Q`; let `N` be the normal closure of the elements
`(tq)^(p^a)`. Then `K ∩ N` has normal subgroups `K₁ ≤ K₂` (normal in `H`) with `K₁` `p`-soluble, `K₂/K₁` a direct
product of `𝔖_p`-groups and `(K ∩ N)/K₂` soluble. -/
theorem CFSGOutsideClean.Wilson.lemma4
    {p : ℕ} [hp : Fact p.Prime]
    {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [hK : K.Normal] (Q : Sylow p K) (t : H) (a : ℕ)
    (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ (a + 1)) = 1) :
    ∃ K₁ K₂ : Subgroup H, K₁.Normal ∧ K₂.Normal ∧ K₁ ≤ K₂ ∧
      K₂ ≤ K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)} ∧
      IsPSolvable p K₁ ∧ SpFactor p K₁ K₂ ∧
      SolFactor K₂ (K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)}) :=
  CFSGOutside.Wilson.lemma4 CFSGComparator.classification.{0} Q t a hexp
