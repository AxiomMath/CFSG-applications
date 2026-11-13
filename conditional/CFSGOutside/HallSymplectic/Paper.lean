import CFSGOutside.HallSymplectic.Main
import CFSGOutside.HallOrthogonal.Defs

/-!
# Hall (2008), Theorem 1.1, alternating case, for subgroups of `V ≃ₗ V`

`eq_symplectic_of_primitive` works in `GL(V)` as units of `End V`. The orthogonal case
(`CFSGOutside.HallOrthogonal`) works in `V ≃ₗ V`. This file transports the alternating case along
`LinearMap.GeneralLinearGroup.generalLinearEquiv`, so both clauses use the same notions of irreducible and primitive
(`CFSGOutside.HallOrthogonal.IsIrreducible`, `IsPrimitive`).
-/

namespace CFSGOutside.HallSymplectic

open Module
open LinearMap (BilinForm)
open CFSGOutside.Corpus CFSGOutside.Corpus.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `Sp(V)`: the linear automorphisms preserving `ω`. -/
def sympGroup (ω : BilinForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, ω (g x) (g y) = ω x y}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simp only [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq] at h
    exact h.symm

/-- A transvection: `g = 1 + φ ⊗ v` with `v ≠ 0`, `φ ≠ 0`, `φ v = 0`. -/
def IsTransvectionEquiv (g : V ≃ₗ[K] V) : Prop :=
  ∃ (v : V) (φ : Dual K V), v ≠ 0 ∧ φ ≠ 0 ∧ φ v = 0 ∧ (g : V →ₗ[K] V) = 1 + φ.smulRight v

/-- The isomorphism `GL(V) ≃* (V ≃ₗ V)`. -/
abbrev glEquiv : LinearMap.GeneralLinearGroup K V ≃* (V ≃ₗ[K] V) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K V

/-- The subgroup of `GL(V)` corresponding to `G`. -/
abbrev toGL (G : Subgroup (V ≃ₗ[K] V)) : Subgroup (LinearMap.GeneralLinearGroup K V) :=
  G.comap glEquiv.toMonoidHom

lemma mem_toGL {G : Subgroup (V ≃ₗ[K] V)} {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ toGL G ↔ glEquiv g ∈ G :=
  Iff.rfl

lemma translates_toGL (G : Subgroup (V ≃ₗ[K] V)) (W : Submodule K V) :
    translates (toGL G) W = HallOrthogonal.translates G W := by
  ext U
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨glEquiv g, hg⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨glEquiv.symm g, by simpa [mem_toGL] using hg⟩, ?_⟩
    rfl

lemma isIrreducibleGroup_toGL {G : Subgroup (V ≃ₗ[K] V)} (h : HallOrthogonal.IsIrreducible G) :
    IsIrreducibleGroup (toGL G) := by
  refine ⟨h.1, fun W hW => h.2 W fun g hg w hw => ?_⟩
  exact hW (glEquiv.symm g) (by simpa [mem_toGL] using hg) w hw

lemma isPrimitiveGroup_toGL {G : Subgroup (V ≃ₗ[K] V)} (h : HallOrthogonal.IsPrimitive G) :
    IsPrimitiveGroup (toGL G) := by
  intro W h0 htop
  rw [translates_toGL]
  exact h W h0 htop

/-- **Hall (2008), Theorem 1.1, alternating case**, for `G ≤ Sp(V)` inside `V ≃ₗ V`: if `ℓ ≥ 3`, `ω` is a
nondegenerate alternating form and `G` is irreducible, primitive and contains a transvection, then
`G = Sp(V)`. -/
theorem theorem_1_1_symplectic [McLaughlinCentres] [AlternatingTransvectionGeneration] {ℓ : ℕ}
    [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V] [FiniteDimensional (ZMod ℓ) V]
    (hℓ : 3 ≤ ℓ) (ω : BilinForm (ZMod ℓ) V) (hω : ω.Nondegenerate) (hωalt : ω.IsAlt)
    (G : Subgroup (V ≃ₗ[ZMod ℓ] V)) (hGω : G ≤ sympGroup ω) (hirr : HallOrthogonal.IsIrreducible G)
    (hprim : HallOrthogonal.IsPrimitive G) (htv : ∃ g ∈ G, IsTransvectionEquiv g) :
    G = sympGroup ω := by
  have hGω' : toGL G ≤ bilinIsometryGroup ω := fun g hg x y => hGω hg x y
  have htv' : ∃ g ∈ toGL G, IsTransvection g := by
    obtain ⟨g, hg, v, φ, hv, hφ, hφv, hgv⟩ := htv
    exact ⟨glEquiv.symm g, by simpa [mem_toGL] using hg, v, φ, hv, hφ, hφv, hgv⟩
  have h := eq_symplectic_of_primitive hℓ ω hω hωalt hGω' (isIrreducibleGroup_toGL hirr)
    (isPrimitiveGroup_toGL hprim) htv'
  refine le_antisymm hGω fun g hg => ?_
  have hmem : glEquiv.symm g ∈ toGL G := h ▸ fun x y => hg x y
  simpa [mem_toGL] using hmem

end CFSGOutside.HallSymplectic
