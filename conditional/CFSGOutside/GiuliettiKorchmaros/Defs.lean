import Mathlib

/-!
# Giulietti–Korchmáros: the group-theoretic hypotheses of §6

M. Giulietti, G. Korchmáros, *Algebraic curves with many automorphisms*, Adv. Math. 349 (2019), §6. Throughout
§6, `G` is an automorphism group of a curve of even genus in odd characteristic. In the proofs of §6.1 this
enters only through Lemma 6.2: every 2-subgroup of `G` has a cyclic subgroup of index (at most) 2.
-/

namespace CFSGOutside.GiuliettiKorchmaros

/-- Every 2-subgroup of `G` has a cyclic subgroup of index at most 2 (the conclusion of Lemma 6.2). -/
def CyclicIndexTwo (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, IsPGroup 2 P → ∃ C : Subgroup G, C ≤ P ∧ IsCyclic C ∧ C.relIndex P ≤ 2

/-- `G` is *odd core-free*: it has no nontrivial normal subgroup of odd order (§6). -/
def OddCoreFree (G : Type*) [Group G] : Prop :=
  ∀ M : Subgroup G, M.Normal → Odd (Nat.card M) → M = ⊥

/-- `N` is a minimal normal subgroup of `G`. -/
def IsMinimalNormal {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N

end CFSGOutside.GiuliettiKorchmaros
