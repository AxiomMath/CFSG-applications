import Mathlib

/-!
# Subgroup perfect codes in Cayley graphs: definitions

X. Ma, G. L. Walls, K. Wang, S. Zhou, *Subgroup perfect codes in Cayley graphs*, SIAM J. Discrete Math. 34
(2020) 1909-1921, DOI 10.1137/19m1258013 (arXiv:1904.01858). Definitions of Cayley graphs, perfect codes and
code-perfect groups, as used in Theorem 1.1 and Corollary 1.4.
-/

namespace CFSGOutside.MaWallsWangZhou

/-- The Cayley graph `Cay(G, S)`: distinct `x, y` are adjacent when `y x⁻¹ ∈ S`
(symmetrized; for inverse-closed `S` this is the usual definition). -/
def cayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G where
  Adj x y := x ≠ y ∧ (y * x⁻¹ ∈ S ∨ x * y⁻¹ ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A perfect code (efficient dominating set) of a graph: an independent set such that every
vertex outside it is adjacent to exactly one of its vertices. -/
def IsPerfectCode {V : Type*} (Γ : SimpleGraph V) (C : Set V) : Prop :=
  (∀ u ∈ C, ∀ v ∈ C, ¬ Γ.Adj u v) ∧ ∀ v ∉ C, ∃! u, u ∈ C ∧ Γ.Adj v u

/-- `C` is a perfect code of the group `G`: it is a perfect code of some Cayley graph
`Cay(G, S)`, `S` inverse-closed and `1 ∉ S`. -/
def IsPerfectCodeOf {G : Type*} [Group G] (C : Set G) : Prop :=
  ∃ S : Set G, S⁻¹ = S ∧ (1 : G) ∉ S ∧ IsPerfectCode (cayleyGraph S) C

/-- A group is *code-perfect* if every subgroup is a perfect code of it. -/
def CodePerfect (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsPerfectCodeOf (H : Set G)

end CFSGOutside.MaWallsWangZhou
