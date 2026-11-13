import CFSGOutside.Corpus.HallPaige.LieSymplectic
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# Corpus input for the unitary groups

The special unitary group `StatedSU n q K` of the corpus and the corpus identification of the
TauCeti carrier of `²A_r(q)` with `PSU_{r+1}(q) = StatedProj (StatedSU (r+1) q 𝔽_{q²})`.

`StatedSU` (CFSG/Open/StatedDefs.lean:49) is written in the corpus as
`matrix_model% CFSG.MatrixModel.unitaryCore (Fin n) K q`; the elaborator `matrix_model%`
(CFSG/Open/MatrixModelCore.lean:9) delta-expands `unitaryCore` (CFSG/Open/MatrixModelCore.lean:24)
and the definition below is that expansion. `StatedScalars` and `StatedProj` are in
`CFSGOutside.Corpus.HallPaige.LieSymplectic`.
-/

namespace CFSGOutside.Corpus.Lie

open Matrix TauCeti

/-- Corpus: `CFSG.Open.StatedSU`, CFSG/Open/StatedDefs.lean:49 (the `matrix_model%` expansion of
`CFSG.MatrixModel.unitaryCore (Fin n) K q`). -/
def StatedSU (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}

/-- The corpus identification of the catalogue group `²A_r(q)` with `PSU_{r+1}(q)`. -/
class UnitaryEquiv : Prop where
  /-- Corpus: `CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj`,
  CFSG/LocalAnalysis/QuasithinUnique/SQTK/UnitaryTauCeti.lean:31, a `def` with exactly this type. -/
  typeTwistedAGroupEquivStatedProj (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) : Nonempty (ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩ ≃*
      StatedProj (StatedSU (r + 1)
        (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
          ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩)
        (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩)
          (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩))))

/-- The corpus declaration `typeTwistedAGroupEquivStatedProj` is a `def` of this type; here it is chosen from the field of `UnitaryEquiv`. -/
noncomputable def typeTwistedAGroupEquivStatedProj [Corpus.Lie.UnitaryEquiv] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩ ≃*
      StatedProj (StatedSU (r + 1)
        (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
          ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩)
        (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩)
          (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩))) :=
  Classical.choice (Corpus.Lie.UnitaryEquiv.typeTwistedAGroupEquivStatedProj r q hv)

end CFSGOutside.Corpus.Lie
