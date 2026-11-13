import CFSGOutside.Hall.Paper
import CFSGOutsideClean.Corpus.ZSUseInput
import CFSGOutsideClean.Corpus.GGSecFiveRootRefl
import CFSGOutsideClean.Corpus.GGSecFiveCoxProd
import CFSGOutsideClean.Corpus.ReflectMulReflectClosure
import CFSGOutsideClean.Corpus.McLaughlinCentres
import CFSGOutsideClean.Corpus.AlternatingTransvectionGeneration

/-! Hall (2008), Theorem 1.1, with the Zalesskiĭ–Serežkin classification, the Weyl-group inputs, the
norm-class generation of reflections, McLaughlin's theorem and the generation of `Sp(V)` by transvections
supplied by the corpus. -/

namespace CFSGOutsideClean.Hall

open QuadraticMap
open CFSGOutside.HallOrthogonal CFSGOutside.HallSymplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- **Big monodromy.** Let ℓ be a prime and V a finite-dimensional vector space over 𝔽_ℓ. Call a subgroup G of GL(V)
irreducible if V ≠ 0 has no proper nonzero G-invariant subspace, and primitive if V is not the direct sum of the
distinct G-translates of a proper nonzero subspace. (a) If ℓ ≥ 5, Q is a quadratic form on V with nondegenerate
polar form, and G ≤ O(Q) is irreducible, primitive, and contains a reflection and an isotropic shear (an element σ ≠
1 with (σ − 1)² = 0), then G is O(Q), the kernel of the spinor norm, or the subgroup of elements whose spinor norm
is trivial exactly when their determinant is 1. (b) If ℓ ≥ 3, ω is a nondegenerate alternating form on V, and G ≤
Sp(ω) is irreducible, primitive, and contains a transvection, then G = Sp(ω).

Source: C. Hall, Big symplectic or orthogonal monodromy modulo ℓ, Duke Math. J. 141 (2008), 179–203, Theorem 1.1.
https://doi.org/10.1215/S0012-7094-08-14115-8 -/
theorem theorem_1_1 {ℓ : ℕ} [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V]
    [FiniteDimensional (ZMod ℓ) V] :
    (∀ [Invertible (2 : ZMod ℓ)], 5 ≤ ℓ → ∀ (Q : QuadraticForm (ZMod ℓ) V)
      (hQ : (polarBilin Q).Nondegenerate) (G : Subgroup (V ≃ₗ[ZMod ℓ] V)), G ≤ orthGroup Q →
      IsIrreducible G → IsPrimitive G → (∃ g ∈ G, IsReflection Q g) → (∃ σ ∈ G, IsIsotropicShear Q σ) →
      G = orthGroup Q ∨
        (∀ g (hg : g ∈ orthGroup Q), g ∈ G ↔
          CliffordAlgebra.orthogonalSpinorNorm Q (nondegenerate_polar_iff.mp hQ) ⟨g, hg⟩ = 1) ∨
        (∀ g (hg : g ∈ orthGroup Q), g ∈ G ↔
          (CliffordAlgebra.orthogonalSpinorNorm Q (nondegenerate_polar_iff.mp hQ) ⟨g, hg⟩ = 1 ↔
            LinearEquiv.det g = 1))) ∧
    (3 ≤ ℓ → ∀ (ω : LinearMap.BilinForm (ZMod ℓ) V), ω.Nondegenerate → ω.IsAlt →
      ∀ G : Subgroup (V ≃ₗ[ZMod ℓ] V), G ≤ sympGroup ω → IsIrreducible G → IsPrimitive G →
      (∃ g ∈ G, IsTransvectionEquiv g) → G = sympGroup ω) :=
  CFSGOutside.Hall.theorem_1_1

end CFSGOutsideClean.Hall
