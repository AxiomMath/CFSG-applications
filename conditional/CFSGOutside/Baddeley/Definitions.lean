import Mathlib

/-!
# Baddeley, two-arc transitive graphs: definitions

R. W. Baddeley, *Two-arc transitive graphs and twisted wreath products*, J. Algebraic Combin. **2** (1993),
215–237, DOI 10.1023/A:1022447514654.

**Definition 1.1 (p. 216).** `(Γ, G)` is a *pair* if `Γ` is a graph admitting `G` as a group of automorphisms.
The pair is *nice* if `Γ` is connected and `G` is transitive on the 2-arcs of `Γ`; it is *special* if, in addition,
`G` has a minimal normal subgroup `M` that is both nonabelian and regular on the vertices of `Γ`.

All graphs of the paper are finite, undirected and loopless (p. 217): here `Γ : SimpleGraph V` with `V` finite. A
group of automorphisms of `Γ` is a subgroup `G` of `Equiv.Perm V` whose elements preserve adjacency. A 2-arc is a
sequence `(a₀, a₁, a₂)` of vertices with `a₀ ~ a₁ ~ a₂` and `a₀ ≠ a₂` (p. 215). The definitions are stated for any
group `X` acting on `V`, so that they apply both to subgroups of `Equiv.Perm V` and to the group `G` itself.
-/

namespace CFSGOutside.Baddeley

open Subgroup

variable {X : Type*} [Group X]

/-- `N` is a minimal normal subgroup of the subgroup `K`: a nontrivial subgroup of `K`, normalized by `K`,
containing no nontrivial subgroup normalized by `K` other than itself. -/
def IsMinimalNormalIn (N K : Subgroup X) : Prop :=
  N ≤ K ∧ K ≤ normalizer (N : Set X) ∧ N ≠ ⊥ ∧
    ∀ L : Subgroup X, L ≤ N → K ≤ normalizer (L : Set X) → L = ⊥ ∨ L = N

/-- `N` is nonabelian. -/
def IsNonabelian (N : Subgroup X) : Prop :=
  ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a

variable (V : Type*) [MulAction X V]

/-- `N` is regular on `V`: transitive, and only the identity fixes a point. -/
def IsRegular (N : Subgroup X) : Prop :=
  (∀ v w : V, ∃ m ∈ N, m • v = w) ∧ ∀ m ∈ N, ∀ v : V, m • v = v → m = 1

variable {V} (Γ : SimpleGraph V)

/-- Every element of `G` is an automorphism of `Γ`. -/
def IsAutGroup (G : Subgroup X) : Prop :=
  ∀ g ∈ G, ∀ u v : V, Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v

/-- `G` is transitive on the 2-arcs `(a₀, a₁, a₂)` of `Γ`. -/
def IsTwoArcTransitive (G : Subgroup X) : Prop :=
  ∀ a₀ a₁ a₂ b₀ b₁ b₂ : V, Γ.Adj a₀ a₁ → Γ.Adj a₁ a₂ → a₀ ≠ a₂ →
    Γ.Adj b₀ b₁ → Γ.Adj b₁ b₂ → b₀ ≠ b₂ → ∃ g ∈ G, g • a₀ = b₀ ∧ g • a₁ = b₁ ∧ g • a₂ = b₂

/-- **Definition 1.1.** `(Γ, G)` is a nice pair. -/
def IsNicePair (G : Subgroup X) : Prop :=
  IsAutGroup Γ G ∧ Γ.Connected ∧ IsTwoArcTransitive Γ G

/-- **Definition 1.1.** `(Γ, G)` is a special pair. -/
def IsSpecialPair (G : Subgroup X) : Prop :=
  IsNicePair Γ G ∧ ∃ M : Subgroup X, IsMinimalNormalIn M G ∧ IsNonabelian M ∧ IsRegular V M

end CFSGOutside.Baddeley
