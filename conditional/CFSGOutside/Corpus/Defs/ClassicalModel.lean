import CFSGOutside.Corpus.Defs.Fitting
import CFSGOutside.Corpus.Defs.ReeModel

/-!
# Copied corpus definitions: models of the classical simple groups, and the `p`-core

Definitions copied from AxiomMath/CFSG at commit 69cb972f587a3ecc035e092253167ff2e303c962, under
`CFSGOutside.Corpus` so that `clean/`, which imports the corpus too, sees no clash. The copies are:

* `Open.pCoreOf` from `CFSG/Open/LocalVocabulary.lean`, built on `pCore` of `CFSGOutside.Corpus.Defs.Fitting`;
* `Open.StatedScalars` to `Open.StatedClassicalModel` from `CFSG/Open/StatedDefs.lean`.

In the corpus, `StatedSU`, `StatedSp`, `StatedOmega`, `StatedQuadPlus` and `StatedQuadMinus` are written with the
elaborator `matrix_model%`, which replaces the constants of `CFSG/Open/MatrixModelCore.lean` (`unitaryCore`,
`gramCore`, `isometryCore`, `plusQuadCore`, `minusQuadCore`) by their bodies. The copies below contain those bodies
directly, so the elaborator is not needed. `StatedLieTag` and `StatedLieAdmissible` are in
`CFSGOutside.Corpus.Defs.ReeModel`. The clean build proves each copy equal to its original in
`clean/CFSGOutsideClean/Corpus/Defs/ClassicalModel.lean`.
-/

namespace CFSGOutside.Corpus

namespace Open

open Matrix

/-- The `p`-core of `H`, as a subgroup of `G`. Copy of `CFSG.Open.pCoreOf`, `CFSG/Open/LocalVocabulary.lean`
line 26. -/
def pCoreOf (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (pCore p H).map H.subtype

/-- The scalar matrices in `GL ι K`. Copy of `CFSG.Open.StatedScalars`, `CFSG/Open/StatedDefs.lean` line 33. -/
def StatedScalars (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Subgroup (GL ι K) :=
  (Matrix.GeneralLinearGroup.scalar ι).range

/-- The scalar matrices are normal. Copy of `CFSG.Open.StatedScalars.normal`, `CFSG/Open/StatedDefs.lean`
line 37. -/
instance StatedScalars.normal (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (StatedScalars ι K).Normal := by
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

/-- A subgroup of `GL ι K` modulo the scalars. Copy of `CFSG.Open.StatedProj`, `CFSG/Open/StatedDefs.lean`
line 42. -/
abbrev StatedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Type :=
  H ⧸ (StatedScalars ι K).subgroupOf H

/-- The special linear group, as a subgroup of `GL (Fin n) K`. Copy of `CFSG.Open.StatedSL`,
`CFSG/Open/StatedDefs.lean` line 46. -/
def StatedSL (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1}

/-- The special unitary group. Copy of `CFSG.Open.StatedSU`, `CFSG/Open/StatedDefs.lean` line 49, with
`CFSG.MatrixModel.unitaryCore` unfolded. -/
def StatedSU (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}

/-- The symplectic group. Copy of `CFSG.Open.StatedSp`, `CFSG/Open/StatedDefs.lean` line 52, with
`CFSG.MatrixModel.gramCore` unfolded. -/
def StatedSp (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n ⊕ Fin n) K) :=
  Subgroup.closure {A |
    @HMul.hMul (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) instHMul
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)}

/-- The commutator subgroup of the isometry group of the quadratic form `Q`. Copy of `CFSG.Open.StatedOmega`,
`CFSG/Open/StatedDefs.lean` line 56, with `CFSG.MatrixModel.isometryCore` unfolded. -/
def StatedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  ⁅Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v},
    Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v}⁆

/-- The quadratic form of odd dimension. Copy of `CFSG.Open.StatedQuadOdd`, `CFSG/Open/StatedDefs.lean`
line 60. -/
def StatedQuadOdd (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n ⊕ Unit → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) ^ 2

/-- The hyperbolic quadratic form. Copy of `CFSG.Open.StatedQuadPlus`, `CFSG/Open/StatedDefs.lean` line 63,
with `CFSG.MatrixModel.plusQuadCore` unfolded. -/
def StatedQuadPlus (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) : K :=
  ∑ i : Fin n, v (Sum.inl i) * v (Sum.inr i)

/-- The elliptic quadratic form. Copy of `CFSG.Open.StatedQuadMinus`, `CFSG/Open/StatedDefs.lean` line 66,
with `CFSG.MatrixModel.minusQuadCore` unfolded. -/
def StatedQuadMinus (n : ℕ) (K : Type) [Field K] (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) : K :=
  ∑ i : Fin (n - 1), v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
    b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2

/-- `G` is isomorphic to a finite simple classical group of type `t` over `𝔽_{p^f}`. Copy of
`CFSG.Open.StatedClassicalModel`, `CFSG/Open/StatedDefs.lean` line 70. -/
def StatedClassicalModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  StatedLieAdmissible t n p f ∧
  match t with
  | .PSL => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSL n K))
  | .PSU => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
      Nonempty (G ≃* StatedProj (StatedSU n (p ^ f) K))
  | .PSp => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSp n K))
  | .POmegaOdd => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
  | .POmegaPlus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
  | .POmegaMinus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
  | _ => False

end Open

end CFSGOutside.Corpus
