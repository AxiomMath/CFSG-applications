import Mathlib

/-!
# Copied corpus definitions: root groups of transvections (McLaughlin)

Copied verbatim from `CFSG/ClassicalGroups/McLaughlin/Basic.lean` (lines 22, 26, 30, 84) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus`.
-/

namespace CFSGOutside.Corpus.ClassicalGroups.McLaughlin

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Copy of `CFSG.ClassicalGroups.McLaughlin.IsRootElt`: `φ v = 0` and the whole root group `{1 + c φ ⊗ v}` lies
in `X`. -/
def IsRootElt (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) (φ : Dual K V) :
    Prop :=
  φ v = 0 ∧ ∀ c : K, ∃ g ∈ X, (g : V →ₗ[K] V) = 1 + c • φ.smulRight v

/-- Copy of `CFSG.ClassicalGroups.McLaughlin.GenByRoots`. -/
def GenByRoots (X : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop :=
  X = Subgroup.closure {g : LinearMap.GeneralLinearGroup K V | ∃ (v : V) (φ : Dual K V),
    v ≠ 0 ∧ φ ≠ 0 ∧ IsRootElt X v φ ∧ (g : V →ₗ[K] V) = 1 + φ.smulRight v}

/-- Copy of `CFSG.ClassicalGroups.McLaughlin.Irred`. -/
def Irred (X : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop :=
  ∀ W : Submodule K V, (∀ g ∈ X, ∀ w ∈ W, (g : V →ₗ[K] V) w ∈ W) → W = ⊥ ∨ W = ⊤

/-- Copy of `CFSG.ClassicalGroups.McLaughlin.IsCentre`. -/
def IsCentre (X : Subgroup (LinearMap.GeneralLinearGroup K V)) (v : V) : Prop :=
  v ≠ 0 ∧ ∃ φ : Dual K V, φ ≠ 0 ∧ IsRootElt X v φ

end CFSGOutside.Corpus.ClassicalGroups.McLaughlin
