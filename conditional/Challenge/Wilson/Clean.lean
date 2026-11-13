import CFSGOutside.Wilson.Defs

/-!
# Wilson, Theorem 2\* and Lemma 4(ii)

J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66 (EuDML 178137).

**Theorem 2\*** (p. 62). Let `p` be a prime and `K` a normal subgroup of a finite group `H`. If a Sylow
`p`-subgroup `Q` of `K` has a coset `tQ` in `H` of exponent dividing `p^a`, then `K` has a series
`1 = K₀ ≤ K₁ ≤ ⋯ ≤ K_{2a+1} = K` such that `K_i/K_{i-1}` is `p`-soluble for `i` odd and is a direct product of
non-abelian simple groups of order divisible by `p` for `i` even. The series formalized consists of subgroups
normal in `H`.

**Lemma 4(ii)** (p. 63), with `a + 1` in place of `a`. With `N` the normal closure of the elements `(tq)^(p^a)`,
`K ∩ N` has normal subgroups `K₁ ≤ K₂` with `K₁` `p`-soluble, `K₂/K₁` a direct product of `𝔖_p`-groups and
`(K ∩ N)/K₂` soluble.

Both hold unconditionally, using the classification of finite simple groups.
-/

open Subgroup CFSGOutside.Corpus CFSGOutside.Wilson

theorem CFSGOutsideClean.Wilson.wilson_theorem2star {p : ℕ}
    [Fact p.Prime] {H : Type} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    (Q : Sylow p K) (t : H) (a : ℕ) (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ a) = 1) :
    ∃ S : ℕ → Subgroup H, S 0 = ⊥ ∧ S (2 * a + 1) = K ∧ (∀ i, (S i).Normal) ∧
      (∀ i < 2 * a + 1, S i ≤ S (i + 1)) ∧
      (∀ i ≤ a, ∃ _ : ((S (2 * i)).subgroupOf (S (2 * i + 1))).Normal,
        IsPSolvable p (S (2 * i + 1) ⧸ (S (2 * i)).subgroupOf (S (2 * i + 1)))) ∧
      (∀ i < a, ∃ _ : ((S (2 * i + 1)).subgroupOf (S (2 * i + 2))).Normal,
        IsSpProd p (S (2 * i + 2) ⧸ (S (2 * i + 1)).subgroupOf (S (2 * i + 2)))) := sorry

theorem CFSGOutsideClean.Wilson.lemma4
    {p : ℕ} [hp : Fact p.Prime]
    {H : Type} [Group H] [Finite H]
    {K : Subgroup H} [hK : K.Normal] (Q : Sylow p K) (t : H) (a : ℕ)
    (hexp : ∀ q ∈ Q, (t * (q : H)) ^ (p ^ (a + 1)) = 1) :
    ∃ K₁ K₂ : Subgroup H, K₁.Normal ∧ K₂.Normal ∧ K₁ ≤ K₂ ∧
      K₂ ≤ K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)} ∧
      IsPSolvable p K₁ ∧ SpFactor p K₁ K₂ ∧
      SolFactor K₂ (K ⊓ normalClosure {x : H | ∃ q ∈ Q, x = (t * (q : H)) ^ (p ^ a)}) := sorry
