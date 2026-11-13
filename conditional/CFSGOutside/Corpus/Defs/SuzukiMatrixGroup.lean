import Mathlib

/-!
# Copied corpus definitions: the Suzuki matrix group

Verbatim copies, under `CFSGOutside.Corpus`, of the definitions in
`CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/MatrixGroups/Suzuki.lean` (lines 31–119) and
`CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/PFAppendixIII/Basic.lean` (line 23) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. `clean/CFSGOutsideClean/Corpus/Defs/SuzukiMatrixGroup.lean` shows
each copy equals its original. `SuzukiMatrixGroup m` is the concrete model of `Sz(2 ^ (2m+1))` in
`GL₄(GF(2 ^ (2m+1)))`.
-/

open scoped MatrixGroups

noncomputable section

namespace CFSGOutside.Corpus

/-- Copy of `CFSG.BenderSuzuki.PFAppendixIII.BinaryGaloisField`. -/
abbrev BinaryGaloisField (m : ℕ) : Type :=
  GaloisField 2 m

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiRootMatrix`. -/
def SuzukiRootMatrix (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![1, a, b, a ^ (2 + 2 ^ (m + 1)) + a * b + b ^ (2 ^ (m + 1));
     0, 1, a ^ (2 ^ (m + 1)), a ^ (1 + 2 ^ (m + 1)) + b;
     0, 0, 1, a;
     0, 0, 0, 1]

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiTorusMatrix`. -/
def SuzukiTorusMatrix (m : ℕ)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m)), 0, 0, 0;
     0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m)), 0, 0;
     0, 0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m))⁻¹, 0;
     0, 0, 0,
       ((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m))⁻¹]

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiWeylMatrix`. -/
def SuzukiWeylMatrix (m : ℕ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiRootGL`. -/
def SuzukiRootGL (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SuzukiRootMatrix m a b) (by
    classical
    have htri : (SuzukiRootMatrix m a b).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SuzukiRootMatrix] at hij ⊢
    rw [Matrix.det_of_isUpperTriangular htri]
    simp [SuzukiRootMatrix, Fin.prod_univ_four])

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiTorusGL`. -/
def SuzukiTorusGL (m : ℕ)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SuzukiTorusMatrix m x) (by
    classical
    have htri : (SuzukiTorusMatrix m x).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SuzukiTorusMatrix] at hij ⊢
    rw [Matrix.det_of_isUpperTriangular htri]
    have hx_sigma :
        (x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    have hx_outer :
        (x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    simp [SuzukiTorusMatrix, Fin.prod_univ_four, hx_sigma, hx_outer])

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiWeylGL`. -/
def SuzukiWeylGL (m : ℕ) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  { val := SuzukiWeylMatrix m
    inv := SuzukiWeylMatrix m
    val_inv := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] }

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGeneratorSet`. -/
def SuzukiMatrixGeneratorSet (m : ℕ) :
    Set (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  {A | (∃ a b, A = SuzukiRootGL m a b) ∨
    (∃ x, A = SuzukiTorusGL m x) ∨ A = SuzukiWeylGL m}

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixSubgroup`. -/
def SuzukiMatrixSubgroup (m : ℕ) :
    Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  Subgroup.closure (SuzukiMatrixGeneratorSet m)

/-- Copy of `CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup`. -/
abbrev SuzukiMatrixGroup (m : ℕ) :=
  SuzukiMatrixSubgroup m

end CFSGOutside.Corpus

end
