import CFSGOutside.HallOrthogonal.Defs
import CFSGOutside.HallSymplectic.Paper

/-!
# Hall (2008), Theorem 1.1 (unconditional)

C. Hall, *Big symplectic or orthogonal monodromy modulo `ℓ`*, Duke Math. J. 141 (2008), 179–203,
DOI 10.1215/S0012-7094-08-14115-8, Theorem 1.1, both clauses, with no hypotheses beyond the paper's. The
definitions are in `CFSGOutside.HallOrthogonal.Defs` and `CFSGOutside.HallSymplectic.Paper`.
-/

namespace CFSGOutsideClean.Hall

open QuadraticMap
open CFSGOutside.HallOrthogonal CFSGOutside.HallSymplectic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

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
      (∃ g ∈ G, IsTransvectionEquiv g) → G = sympGroup ω) := sorry

end CFSGOutsideClean.Hall
