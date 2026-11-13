import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# Corpus input for the groups of type `A`

The corpus identification of the TauCeti carrier of `A_r(q)` with Mathlib's projective special
linear group `PSL_{r+1}(𝔽_q)`, stated as a class with the type of the corpus declaration.
-/

namespace CFSGOutside.Corpus.Lie

open Matrix TauCeti

/-- The corpus identification of the catalogue group `A_r(q)` with `PSL_{r+1}(𝔽_q)`. -/
class TypeAEquiv : Prop where
  /-- Corpus: `CFSG.ClassicalModels.linearCatalogCandidateEquivPSL`,
  CFSG/Adapters/LinearCatalog.lean:20 (AxiomMath/CFSG @ 69cb972), a `def` with exactly this type.
  The TauCeti candidate group of `A_r(q)` is `PSL_{r+1}(𝔽_q)`. -/
  linearCatalogCandidateEquivPSL
    (r : ℕ) (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.A r q).Valid) : Nonempty ((ValidLieTypeIndex.Group ⟨LieTypeIndex.A r q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent))

/-- The corpus declaration `linearCatalogCandidateEquivPSL` is a `def` of this type; here it is chosen from the field of `TypeAEquiv`. -/
noncomputable def linearCatalogCandidateEquivPSL [Corpus.Lie.TypeAEquiv]
    (r : ℕ) (q : PrimePower) [Fact q.p.Prime]
    (hv : (LieTypeIndex.A r q).Valid) :
    (ValidLieTypeIndex.Group ⟨LieTypeIndex.A r q, hv⟩) ≃*
      ProjectiveSpecialLinearGroup (Fin (r + 1)) (GaloisField q.p q.exponent) :=
  Classical.choice (Corpus.Lie.TypeAEquiv.linearCatalogCandidateEquivPSL r q hv)

end CFSGOutside.Corpus.Lie
