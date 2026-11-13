import CFSGOutside.Corpus.HallPaige.LieSymplectic
import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

/-!
# Corpus input for the orthogonal groups

The corpus models `PΩ_{2r+1}(k)`, `PΩ⁺_{2r}(k)`, `PΩ⁻_{2r}(k)` (the commutator subgroup of the
isometry group of the standard quadratic form, modulo scalars) and the corpus identifications of
the TauCeti carriers of `B_r(q)` (`q` odd, `r ≥ 3`), `D_r(q)` and `²D_r(q)` with them, over the
fixed field of the index.

Definitions copied from AxiomMath/CFSG @ 69cb972, CFSG/Open/StatedDefs.lean: `StatedOmega` (:56),
`StatedQuadOdd` (:60) verbatim, `StatedQuadPlus` (:63) and `StatedQuadMinus` (:66), which the
corpus writes with the elaborator `matrix_model%` (CFSG/Open/MatrixModelCore.lean:9); it
delta-expands `isometryCore` (:32), `plusQuadCore` (:44) and `minusQuadCore` (:48) of
CFSG/Open/MatrixModelCore.lean, and the definitions below are those expansions. `StatedScalars`
and `StatedProj` are in `CFSGOutside.Corpus.HallPaige.LieSymplectic`.
-/

namespace CFSGOutside.Corpus.Lie

open Matrix TauCeti

/-- Corpus: `CFSG.Open.StatedOmega`, CFSG/Open/StatedDefs.lean:56 (the `matrix_model%`
expansion of `⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆`). -/
def StatedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  ⁅Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v},
    Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v}⁆

/-- Corpus: `CFSG.Open.StatedQuadOdd`, CFSG/Open/StatedDefs.lean:60. -/
def StatedQuadOdd (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n ⊕ Unit → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) ^ 2

/-- Corpus: `CFSG.Open.StatedQuadPlus`, CFSG/Open/StatedDefs.lean:63 (the `matrix_model%`
expansion of `CFSG.MatrixModel.plusQuadCore n K v`). -/
def StatedQuadPlus (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) : K :=
  ∑ i : Fin n, v (Sum.inl i) * v (Sum.inr i)

/-- Corpus: `CFSG.Open.StatedQuadMinus`, CFSG/Open/StatedDefs.lean:66 (the `matrix_model%`
expansion of `CFSG.MatrixModel.minusQuadCore (n - 1) K b c v`). -/
def StatedQuadMinus (n : ℕ) (K : Type) [Field K] (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) : K :=
  ∑ i : Fin (n - 1), v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2

/-- The corpus identifications of the orthogonal catalogue groups. -/
class OrthEquivs : Prop where
  /-- Corpus: `CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd`,
  CFSG/RankThree/PartTwo/Census/Carrier/SpinBOdd.lean:26, a `def` with exactly this type. -/
  typeBGroupEquivStatedProj_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p ≠ 2) (hr : 3 ≤ r) : Nonempty (ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadOdd r ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩))))
  /-- Corpus: `CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid`,
  CFSG/RankThree/PartTwo/Census/Carrier/SpinDOdd.lean:157, a `def` with exactly this type. -/
  typeDGroupEquivStatedProj_of_valid (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) : Nonempty (ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadPlus r ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩))))
  /-- Corpus:
  `CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid`,
  CFSG/RankThree/PartTwo/Census/Carrier/SpinTDOdd.lean:195. -/
  exists_typeTwistedDGroupEquivStatedProj_of_valid (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) :
    ∃ b c : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩),
      (∀ s, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩ ≃*
          StatedProj (StatedOmega
            (StatedQuadMinus r ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c)))

/-- The corpus declaration `typeBGroupEquivStatedProj_odd` is a `def` of this type; here it is chosen from the field of `OrthEquivs`. -/
noncomputable def typeBGroupEquivStatedProj_odd [Corpus.Lie.OrthEquivs] (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hp : q.p ≠ 2) (hr : 3 ≤ r) :
    ValidLieTypeIndex.Group ⟨.B r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadOdd r ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩))) :=
  Classical.choice (Corpus.Lie.OrthEquivs.typeBGroupEquivStatedProj_odd r q hv hp hr)

/-- The corpus declaration `typeDGroupEquivStatedProj_of_valid` is a `def` of this type; here it is chosen from the field of `OrthEquivs`. -/
noncomputable def typeDGroupEquivStatedProj_of_valid [Corpus.Lie.OrthEquivs] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) :
    ValidLieTypeIndex.Group ⟨.D r q, hv⟩ ≃*
      StatedProj (StatedOmega
        (StatedQuadPlus r ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩))) :=
  Classical.choice (Corpus.Lie.OrthEquivs.typeDGroupEquivStatedProj_of_valid r q hv)

end CFSGOutside.Corpus.Lie
