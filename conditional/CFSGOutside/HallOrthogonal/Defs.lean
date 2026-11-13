import Mathlib
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

/-!
# Hall (2008), Theorem 1.1, orthogonal case: the notions in the statement

C. Hall, *Big symplectic or orthogonal monodromy modulo `ℓ`*, Duke Math. J. 141 (2008), §3. `V` is a vector
space over `F_ℓ` with a perfect symmetric pairing, here the polar form `⟨w, v⟩ = polar Q w v` of a quadratic
form `Q`, and `Γ = O(V)` is its isometry group, TauCeti's `orthogonalGroup Q`.

* The *drop* of `γ` is the codimension of the fixed space `V^{γ = 1}`.
* A *reflection* is an element of `Γ` of drop `1` and determinant `-1`.
* An *isotropic shear* is a nontrivial unipotent `σ ∈ Γ` with `(σ - 1)² = 0`.
* `G` is *irreducible* if `V` is an irreducible `G`-representation.
* `G` is *primitive* if `V` is not induced from a proper subgroup. Equivalently (Hall, §3, citing [CR 12.D]),
  there is no nontrivial proper `W` such that `V` is the direct sum of the distinct `G`-translates of `W`.
-/

namespace CFSGOutside.HallOrthogonal

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `Γ = O(V)`, the isometries of `Q`. -/
abbrev orthGroup (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q

/-- The fixed space `V^{γ = 1}`. -/
def fixSpace (g : V ≃ₗ[K] V) : Submodule K V := LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)

/-- The drop of `γ`: the codimension of `V^{γ = 1}`. -/
noncomputable def drop (g : V ≃ₗ[K] V) : ℕ := finrank K V - finrank K (fixSpace g)

/-- A reflection: an element of `Γ` of drop `1` and determinant `-1`. -/
def IsReflection (Q : QuadraticForm K V) (g : V ≃ₗ[K] V) : Prop :=
  g ∈ orthGroup Q ∧ drop g = 1 ∧ LinearEquiv.det g = -1

/-- An isotropic shear: a nontrivial unipotent `σ ∈ Γ` with `(σ - 1)² = 0`. -/
def IsIsotropicShear (Q : QuadraticForm K V) (σ : V ≃ₗ[K] V) : Prop :=
  σ ∈ orthGroup Q ∧ σ ≠ 1 ∧ IsNilpotent ((σ : V →ₗ[K] V) - 1) ∧ ((σ : V →ₗ[K] V) - 1) ^ 2 = 0

/-- `W` is invariant under every element of `H`. -/
def IsInvariant (H : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V) : Prop :=
  ∀ g ∈ H, ∀ w ∈ W, g w ∈ W

/-- `G` is irreducible: `V ≠ 0` and the only `G`-invariant subspaces are `0` and `V`. -/
def IsIrreducible (G : Subgroup (V ≃ₗ[K] V)) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule K V, IsInvariant G W → W = ⊥ ∨ W = ⊤

/-- The set of `G`-translates `gW` of a subspace `W`. -/
def translates (G : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V) : Set (Submodule K V) :=
  Set.range fun g : G => W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V)

/-- `G` is primitive: no nontrivial proper `W` has `V` as the direct sum of its distinct `G`-translates. -/
def IsPrimitive (G : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∀ W : Submodule K V, W ≠ ⊥ → W ≠ ⊤ →
    ¬ (sSupIndep (translates G W) ∧ sSup (translates G W) = ⊤)

end CFSGOutside.HallOrthogonal
