import CFSGOutside.HallOrthogonal.Defs
import CFSGOutside.HallSymplectic.Paper
import CFSGOutside.Corpus.ZSUseInput
import CFSGOutside.Corpus.GGSecFiveRootRefl
import CFSGOutside.Corpus.GGSecFiveCoxProd
import CFSGOutside.Corpus.ReflectMulReflectClosure

/-!
# Hall (2008), Theorem 1.1 (fast path)

C. Hall, *Big symplectic or orthogonal monodromy modulo `ℓ`*, Duke Math. J. 141 (2008), 179–203,
DOI 10.1215/S0012-7094-08-14115-8, Theorem 1.1: "Let `V` be an `F_ℓ`-vector space together with a perfect pairing
`V × V → F_ℓ` and let `G ≤ GL(V)` be an irreducible primitive subgroup which preserves the pairing. If the pairing
is symmetric, `G` contains a reflection and an isotropic shear, and `ℓ ≥ 5`, then `G` is one of the following:
the full orthogonal group `O(V)`; the kernel of the spinor norm; the kernel of the product of the spinor norm and
the determinant. If the pairing is alternating, `G` contains a transvection, and `ℓ ≥ 3`, then `G` is all of the
symplectic group `Sp(V)`."

Both clauses are stated for subgroups of `V ≃ₗ V`, with the same notions of irreducible and primitive. A perfect
symmetric pairing over `F_ℓ`, `ℓ` odd, is the polar form of a nondegenerate quadratic form.
-/

namespace CFSGOutside.Hall

open QuadraticMap
open CFSGOutside.HallOrthogonal CFSGOutside.HallSymplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- **Hall (2008), Theorem 1.1**, both clauses. -/
theorem theorem_1_1 [CFSGOutside.Corpus.ZSUseInput] [CFSGOutside.Corpus.GGSecFiveRootRefl]
    [CFSGOutside.Corpus.GGSecFiveCoxProd] [CFSGOutside.Corpus.ReflectMulReflectClosure]
    [CFSGOutside.Corpus.McLaughlinCentres] [CFSGOutside.Corpus.AlternatingTransvectionGeneration]
    {ℓ : ℕ} [Fact ℓ.Prime] {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V] [FiniteDimensional (ZMod ℓ) V] :
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
      (∃ g ∈ G, IsTransvectionEquiv g) → G = sympGroup ω) := sorry

end CFSGOutside.Hall
