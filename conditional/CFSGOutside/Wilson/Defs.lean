import CFSGOutside.Corpus.Defs.PSolvable

/-!
# Wilson, compact torsion groups: definitions

**Paper.** J. S. Wilson, *On the structure of compact torsion groups*, Monatsh. Math. **96** (1983), 57–66
(EuDML 178137), p. 62 (Theorem 2\*) and p. 63 (Lemma 4).

The class `𝔖_p` of the paper consists of the direct products of nonabelian simple groups of order divisible by
`p`. A section `B/A` of a group `H` is a pair of subgroups with `A` normal in `B`.
-/

namespace CFSGOutside.Wilson

open Subgroup

/-- `Y` is isomorphic to a finite direct product of nonabelian simple groups of order divisible by `p`: the class
`𝔖_p` of Wilson (Monatsh. Math. 96 (1983), p. 62, in the statement of Theorem 2\*). The empty product is allowed. -/
def IsSpProd (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (ι : Type) (S : ι → Type) (_ : ∀ i, Group (S i)), Finite ι ∧
    (∀ i, IsSimpleGroup (S i)) ∧ (∀ i, ∃ a b : S i, a * b ≠ b * a) ∧
    (∀ i, p ∣ Nat.card (S i)) ∧ Nonempty (Y ≃* ∀ i, S i)

variable {H : Type} [Group H]

/-- The section `B/A` of `H` is a direct product of `𝔖_p`-groups (Wilson, Theorem 2\*, even-indexed factors). -/
def SpFactor (p : ℕ) (A B : Subgroup H) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, IsSpProd p (B ⧸ A.subgroupOf B)

/-- The section `B/A` of `H` is soluble (Wilson, Lemma 4(ii), the factor `(K ∩ N)/K₂`). -/
def SolFactor (A B : Subgroup H) : Prop :=
  ∃ _ : (A.subgroupOf B).Normal, Group.IsSolvable (B ⧸ A.subgroupOf B)

end CFSGOutside.Wilson
