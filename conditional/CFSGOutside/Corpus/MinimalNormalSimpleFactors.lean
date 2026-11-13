import CFSGOutside.Corpus.Defs.Conjugate

/-!
# Corpus input: a minimal normal subgroup is a product of conjugate simple groups

Statement of `CFSG.LocalCores.minimal_normal_simple_factors`, copied verbatim from
`CFSG/GroupTheory/LocalCores/MinimalNormal.lean` (line 165, with the section variables of line 143) at
AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962. `conjugate` is the copy in
`CFSGOutside.Corpus.Defs`.

A minimal normal subgroup `N` of a finite group is the internal direct product of conjugate simple subgroups.
The corpus theorem is universe polymorphic, so the class takes the universe of `G` as a parameter. The clean
build provides every instance, in `clean/CFSGOutsideClean/Corpus/MinimalNormalSimpleFactors.lean`.
-/

namespace CFSGOutside.Corpus

/-- A minimal normal subgroup is a direct product of conjugate simple subgroups, as
`CFSG.LocalCores.minimal_normal_simple_factors` states it. -/
class MinimalNormalSimpleFactors.{u} : Prop where
  minimal_normal_simple_factors : ∀ {G : Type u} [Group G] [Finite G] {N : Subgroup G} (_hN : N.Normal)
    (_hN1 : N ≠ ⊥) (_hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N),
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ (∀ i, S i ≤ N) ∧ (∀ i, IsSimpleGroup (S i)) ∧
      (∀ i j, ∃ g : G, S j = conjugate (S i) g) ∧ (∀ i, ((S i).subgroupOf N).Normal) ∧
      ∃ e : ((i : Fin r) → S i) ≃* N,
        ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i

end CFSGOutside.Corpus
