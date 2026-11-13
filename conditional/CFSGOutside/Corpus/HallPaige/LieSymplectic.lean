import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Data.Matrix.Block
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Corpus input for the symplectic groups

The projective symplectic group `PSp_{2r}(k) = Sp_{2r}(k) / (scalars)` of the corpus, and the
corpus theorems identifying the TauCeti carriers of `C_r(q)`, `B_2(q)` and `B_r(q)` (`q` even,
`r ≥ 3`) with it.

Definitions copied from AxiomMath/CFSG @ 69cb972, CFSG/Open/StatedDefs.lean: `StatedScalars`
(:33), `StatedScalars.normal` (:37), `StatedProj` (:42) verbatim, and `StatedSp` (:52), which the
corpus writes as `matrix_model% CFSG.MatrixModel.gramCore J`; the elaborator `matrix_model%`
(CFSG/Open/MatrixModelCore.lean:9) delta-expands `gramCore` (CFSG/Open/MatrixModelCore.lean:38),
and the definition below is that expansion.
-/

namespace CFSGOutside.Corpus.Lie

open Matrix

/-- Corpus: `CFSG.Open.StatedScalars`, CFSG/Open/StatedDefs.lean:33. -/
def StatedScalars (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Subgroup (GL ι K) :=
  (Matrix.GeneralLinearGroup.scalar ι).range

/-- Corpus: `CFSG.Open.StatedScalars.normal`, CFSG/Open/StatedDefs.lean:37. -/
instance StatedScalars.normal (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (StatedScalars ι K).Normal := by
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

/-- Corpus: `CFSG.Open.StatedProj`, CFSG/Open/StatedDefs.lean:42. -/
abbrev StatedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Type :=
  H ⧸ (StatedScalars ι K).subgroupOf H

/-- Corpus: `CFSG.Open.StatedSp`, CFSG/Open/StatedDefs.lean:52 (the `matrix_model%` expansion
of `CFSG.MatrixModel.gramCore (fromBlocks 0 1 (-1) 0)`). -/
def StatedSp (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n ⊕ Fin n) K) :=
  Subgroup.closure {A |
    @HMul.hMul (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      instHMul (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)}

/-- The corpus identifications of the symplectic and `B` catalogue groups. -/
class SymplecticEquivs : Prop where
  /-- Corpus: `CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj`,
  CFSG/Adapters/CatalogueFieldBridges/Symplectic.lean:32. -/
  nonempty_mulEquiv_lie_C_of_statedProj {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp r k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.C r q, hv⟩).Group)
  /-- Corpus: `CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj`,
  CFSG/Adapters/CatalogueFieldBridges/Symplectic.lean:47. -/
  nonempty_mulEquiv_lie_B2_of_statedProj {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp 2 k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group)
  /-- Corpus: `CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj`,
  CFSG/Adapters/CatalogueFieldBridges/Symplectic.lean:61. -/
  nonempty_mulEquiv_lie_B_of_statedProj {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p = 2) (hr3 : 3 ≤ r)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = q.card) :
    Nonempty (StatedProj (StatedSp r k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B r q, hv⟩).Group)

end CFSGOutside.Corpus.Lie
