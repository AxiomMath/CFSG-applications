import CFSGOutside.HallPaige.Lie.RankOne
import CFSGOutside.HallPaige.Lie.UnitaryFinite
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# `PSU₃(q)` as a rank-one group

The special unitary group of the hermitian form with Gram matrix
`J = [[0,0,1],[0,1,0],[1,0,0]]` on `K³`, for an involutive automorphism `σ` of `K` with norm and
trace onto the fixed field (`CFSGOutside.HallPaige.Unitary.IsUnitaryInvolution`), is conjugate in `GL₃(K)` to
the special unitary group `SUid σ 3` of the standard form (`CFSGOutside.HallPaige.UnitaryThree.psuEquiv`).
In the `J`-model, with `U` the upper unitriangular, `T` the diagonal elements and
`n = [[0,0,1],[0,-1,0],[1,0,0]]`, we verify the hypotheses of
`CFSGOutside.HallPaige.hasCompleteMapping_of_rankOne_split`: unique Bruhat expressions, and the identity
`t(l) n = u(z σl, l) n u(z, (σl)⁻¹) n u(zl, l)` where `σ(z) z = -(l + σl)/(l σl)`.
-/

namespace CFSGOutside.HallPaige.UnitaryThree

open Matrix Corpus.Lie Unitary

variable {K : Type} [Field K]

/-- The Gram matrix `J`. -/
def Jm : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

variable (σ : K ≃+* K)

/-- The special unitary group of the form with Gram matrix `J`. -/
def SUJ : Subgroup (GL (Fin 3) K) where
  carrier := {B | (B : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
    conjTr σ (B : Matrix (Fin 3) (Fin 3) K) * Jm * (B : Matrix (Fin 3) (Fin 3) K) = Jm}
  mul_mem' {A B} hA hB := by
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], ?_⟩
    rw [Units.val_mul, conjTr_mul]
    calc conjTr σ (B : Matrix (Fin 3) (Fin 3) K) * conjTr σ (A : Matrix (Fin 3) (Fin 3) K) * Jm *
          ((A : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K))
        = conjTr σ (B : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (A : Matrix (Fin 3) (Fin 3) K) * Jm * (A : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = Jm := by rw [hA.2, hB.2]
  one_mem' := ⟨by simp, by simp [conjTr_one]⟩
  inv_mem' {A} hA := by
    have hAB : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hAB
      rw [det_mul, det_one, hA.1, one_mul] at this
      exact this
    · calc conjTr σ ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K) * Jm * ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K)
          = conjTr σ ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K) *
            (conjTr σ (A : Matrix (Fin 3) (Fin 3) K) * Jm * (A : Matrix (Fin 3) (Fin 3) K)) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K) := by rw [hA.2]
        _ = conjTr σ ((A : Matrix _ _ K) * ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K)) * Jm *
            ((A : Matrix _ _ K) * ((A⁻¹ : GL (Fin 3) K) : Matrix _ _ K)) := by
          rw [conjTr_mul]; simp only [Matrix.mul_assoc]
        _ = Jm := by rw [hAB, conjTr_one, Matrix.one_mul, Matrix.mul_one]

section Conj

variable {σ}

/-- The change of basis `C` with `C† C = J`: columns `(1,u,0)`, `(u,u²,u²)`, `(1,0,u)`. -/
def CM (u : K) : Matrix (Fin 3) (Fin 3) K := !![1, u, 1; u, u ^ 2, 0; 0, u ^ 2, u]

theorem conjTr_CM (hinv : ∀ c, σ (σ c) = c) {u : K} (hu : σ u * u = -1) :
    conjTr σ (CM u) * CM u = Jm := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hσu : σ u = -u⁻¹ := by field_simp; linear_combination hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, CM, Jm, Matrix.mul_apply, Fin.sum_univ_three, hσu] <;> field_simp <;> ring

theorem det_Jm : (Jm : Matrix (Fin 3) (Fin 3) K).det = -1 := by
  simp [Jm, det_fin_three]

theorem det_CM_ne_zero (hinv : ∀ c, σ (σ c) = c) {u : K} (hu : σ u * u = -1) :
    (CM u).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (conjTr_CM hinv hu)
  rw [det_mul, h, mul_zero, det_Jm] at this
  exact one_ne_zero (neg_eq_zero.1 this.symm)

/-- `C` as an element of `GL₃`. -/
noncomputable def CG (hinv : ∀ c, σ (σ c) = c) {u : K} (hu : σ u * u = -1) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (CM u) (det_CM_ne_zero hinv hu)

variable (hinv : ∀ c, σ (σ c) = c) {u : K} (hu : σ u * u = -1)

theorem conjTr_CG : conjTr σ ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
    ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Jm := conjTr_CM hinv hu

theorem CG_mul_inv : ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
    (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem CG_inv_mul : (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
    ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- `(C⁻¹)† J C⁻¹ = 1`. -/
theorem conjTr_CGinv_J :
    conjTr σ (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Jm *
      (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← conjTr_CG hinv hu]
  calc conjTr σ (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (conjTr σ ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = conjTr σ (((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (((CG hinv hu : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((CG hinv hu)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [conjTr_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [CG_mul_inv, conjTr_one, Matrix.one_mul]

theorem conj_mem_SUJ {x : GL (Fin 3) K} (hx : x ∈ SUid σ 3) :
    (CG hinv hu)⁻¹ * x * CG hinv hu ∈ SUJ σ := by
  set C := CG hinv hu
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hx.1, mul_one, ← det_mul,
      CG_inv_mul, det_one]
  · rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul]
    calc conjTr σ (C : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (x : Matrix (Fin 3) (Fin 3) K) *
            conjTr σ ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * Jm *
          (((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) *
            (C : Matrix (Fin 3) (Fin 3) K))
        = conjTr σ (C : Matrix (Fin 3) (Fin 3) K) * conjTr σ (x : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Jm *
            ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * (x : Matrix (Fin 3) (Fin 3) K) *
          (C : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = conjTr σ (C : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (x : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *
          (C : Matrix (Fin 3) (Fin 3) K) := by
        rw [conjTr_CGinv_J hinv hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Jm := by rw [hx.2, Matrix.mul_one]; exact conjTr_CG hinv hu

theorem conj_mem_SUid {y : GL (Fin 3) K} (hy : y ∈ SUJ σ) :
    CG hinv hu * y * (CG hinv hu)⁻¹ ∈ SUid σ 3 := by
  set C := CG hinv hu
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hy.1, mul_one, ← det_mul,
      CG_mul_inv, det_one]
  · rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul]
    calc conjTr σ ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (y : Matrix (Fin 3) (Fin 3) K) * conjTr σ (C : Matrix (Fin 3) (Fin 3) K)) *
          ((C : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
            ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = conjTr σ ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (conjTr σ (y : Matrix (Fin 3) (Fin 3) K) *
            (conjTr σ (C : Matrix (Fin 3) (Fin 3) K) * (C : Matrix (Fin 3) (Fin 3) K)) *
            (y : Matrix (Fin 3) (Fin 3) K)) *
          ((C⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [conjTr_CG hinv hu, hy.2]
        exact conjTr_CGinv_J hinv hu

/-- Conjugation by `C` identifies `SUid σ 3` with `SUJ σ`. -/
noncomputable def suEquiv : SUid σ 3 ≃* SUJ σ where
  toFun x := ⟨(CG hinv hu)⁻¹ * x * CG hinv hu, conj_mem_SUJ hinv hu x.2⟩
  invFun y := ⟨CG hinv hu * y * (CG hinv hu)⁻¹, conj_mem_SUid hinv hu y.2⟩
  left_inv x := by ext1; simp [mul_assoc]
  right_inv y := by ext1; simp [mul_assoc]
  map_mul' x y := by ext1; simp [mul_assoc]

theorem conj_scalar {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K) (C : GL (Fin 3) K) :
    C⁻¹ * z * C = z := by
  rw [StatedScalars, ← GeneralLinearGroup.center_eq_range_scalar, Subgroup.mem_center_iff] at hz
  rw [mul_assoc, ← hz C, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_scalar' {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K) (C : GL (Fin 3) K) :
    C * z * C⁻¹ = z := by
  simpa using conj_scalar hz C⁻¹

/-- **`PSU₃` in the `J`-model.** -/
noncomputable def psuEquiv : StatedProj (SUid σ 3) ≃* StatedProj (SUJ σ) :=
  QuotientGroup.congr _ _ (suEquiv hinv hu) (by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (CG hinv hu)⁻¹ * (x : GL (Fin 3) K) * CG hinv hu ∈ StatedScalars (Fin 3) K
      rw [conj_scalar hx]
      exact hx
    · intro hy
      refine ⟨(suEquiv hinv hu).symm y, ?_, by simp⟩
      change CG hinv hu * (y : GL (Fin 3) K) * (CG hinv hu)⁻¹ ∈ StatedScalars (Fin 3) K
      rw [conj_scalar' hy]
      exact hy)

end Conj

section Model

variable {σ}

/-- The matrix of an element of `SUJ σ`. -/
def mat (g : SUJ σ) : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[simp] theorem mat_mul (a b : SUJ σ) : mat (a * b) = mat a * mat b := rfl
@[simp] theorem mat_one : mat (1 : SUJ σ) = 1 := rfl

theorem mat_ext {a b : SUJ σ} (h : mat a = mat b) : a = b := Subtype.ext (Units.ext h)

theorem mat_spec (g : SUJ σ) : conjTr σ (mat g) * Jm * mat g = Jm := g.2.2
theorem mat_det (g : SUJ σ) : (mat g).det = 1 := g.2.1

theorem mat_inv (g : SUJ σ) : mat g⁻¹ = (mat g)⁻¹ := by
  rw [Matrix.inv_eq_right_inv (B := mat g⁻¹)]
  rw [← mat_mul, mul_inv_cancel, mat_one]

/-- An element of `SUJ σ` from a matrix. -/
noncomputable def mkJ (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hJ : conjTr σ M * Jm * M = Jm) : SUJ σ :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero), hdet, hJ⟩

@[simp] theorem mat_mkJ (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hJ : conjTr σ M * Jm * M = Jm) : mat (mkJ M hdet hJ) = M := rfl

variable (σ) in
/-- `u(z, y)`. -/
def uM (z y : K) : Matrix (Fin 3) (Fin 3) K := !![1, -σ z, y; 0, 1, z; 0, 0, 1]

variable (σ) in
/-- `t(l) = diag(l, σl/l, (σl)⁻¹)`. -/
noncomputable def tM (l : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  !![(l : K), 0, 0; 0, σ l / l, 0; 0, 0, (σ l)⁻¹]

/-- The Weyl element. -/
def nM : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

variable (hinv : ∀ c, σ (σ c) = c)
include hinv

theorem uM_det (z y : K) : (uM σ z y).det = 1 := by simp [uM, det_fin_three]

theorem uM_J {z y : K} (h : y + σ y + σ z * z = 0) : conjTr σ (uM σ z y) * Jm * uM σ z y = Jm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, uM, Jm, Matrix.mul_apply, Fin.sum_univ_three, hinv] <;>
    linear_combination h

theorem tM_det (l : Kˣ) : (tM σ l).det = 1 := by
  have h1 : (l : K) ≠ 0 := l.ne_zero
  have h2 : σ (l : K) ≠ 0 := (map_ne_zero σ).2 h1
  simp [tM, det_fin_three]
  field_simp

theorem tM_J (l : Kˣ) : conjTr σ (tM σ l) * Jm * tM σ l = Jm := by
  have h1 : (l : K) ≠ 0 := l.ne_zero
  have h2 : σ (l : K) ≠ 0 := (map_ne_zero σ).2 h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, tM, Jm, Matrix.mul_apply, Fin.sum_univ_three, hinv, map_div₀, map_inv₀] <;>
    field_simp

theorem nM_det : (nM : Matrix (Fin 3) (Fin 3) K).det = 1 := by simp [nM, det_fin_three]

theorem nM_J : conjTr σ (nM : Matrix (Fin 3) (Fin 3) K) * Jm * nM = Jm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, nM, Jm, Matrix.mul_apply, Fin.sum_univ_three]

/-- `u(z, y)` in `SUJ σ`. -/
noncomputable def uJ (z y : K) (h : y + σ y + σ z * z = 0) : SUJ σ :=
  mkJ (uM σ z y) (uM_det hinv z y) (uM_J hinv h)

/-- `n` in `SUJ σ`. -/
noncomputable def nJ : SUJ σ := mkJ nM (nM_det hinv) (nM_J hinv)

/-- `t` as a homomorphism. -/
noncomputable def tHom : Kˣ →* SUJ σ where
  toFun l := mkJ (tM σ l) (tM_det hinv l) (tM_J hinv l)
  map_one' := by
    apply mat_ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tM]
  map_mul' a b := by
    apply mat_ext
    have ha : (a : K) ≠ 0 := a.ne_zero
    have hb : (b : K) ≠ 0 := b.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tM, Matrix.mul_apply, Fin.sum_univ_three, mul_inv] <;> field_simp

@[simp] theorem mat_uJ (z y : K) (h : y + σ y + σ z * z = 0) : mat (uJ hinv z y h) = uM σ z y := rfl
@[simp] theorem mat_nJ : mat (nJ hinv : SUJ σ) = nM := rfl
@[simp] theorem mat_tHom (l : Kˣ) : mat (tHom hinv l : SUJ σ) = tM σ l := rfl

omit hinv in
/-- Equality in `PSU`: up to a nonzero scalar. -/
theorem exists_scalar_of_mk_eq {A B : SUJ σ} (h : (A : StatedProj (SUJ σ)) = (B : StatedProj (SUJ σ))) :
    ∃ c : K, c ≠ 0 ∧ ∀ i j, mat B i j = mat A i j * c := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.ne_zero, fun i j => ?_⟩
  have e : mat B = mat A * Matrix.scalar (Fin 3) (c : K) := by
    have : ((B : SUJ σ) : GL (Fin 3) K) = (A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [hc]; simp
    change ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [this, Units.val_mul, GeneralLinearGroup.coe_scalar]
    rfl
  rw [e, Matrix.scalar_apply, Matrix.mul_diagonal]

end Model

section Groups

variable {σ}

/-- Upper unitriangular matrices. -/
def IsUni (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1

theorem isUni_mul {A B : Matrix (Fin 3) (Fin 3) K} (hA : IsUni A) (hB : IsUni B) :
    IsUni (A * B) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, *]

/-- The inverse of a unitriangular matrix. -/
def uniInv (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, -M 0 1, M 0 1 * M 1 2 - M 0 2; 0, 1, -M 1 2; 0, 0, 1]

theorem mul_uniInv {A : Matrix (Fin 3) (Fin 3) K} (hA : IsUni A) : A * uniInv A = 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniInv, Matrix.mul_apply, Fin.sum_univ_three, *] <;> ring

variable (σ) in
/-- The unitriangular subgroup of `SUJ σ`. -/
def UJ : Subgroup (SUJ σ) where
  carrier := {g | IsUni (mat g)}
  mul_mem' {a b} ha hb := by
    change IsUni (mat (a * b)); rw [mat_mul]; exact isUni_mul ha hb
  one_mem' := by
    change IsUni (mat (1 : SUJ σ)); rw [mat_one]; simp [IsUni]
  inv_mem' {g} hg := by
    change IsUni (mat g⁻¹)
    rw [mat_inv, Matrix.inv_eq_right_inv (mul_uniInv hg)]
    simp [IsUni, uniInv]

theorem mem_UJ {g : SUJ σ} : g ∈ UJ σ ↔ IsUni (mat g) := Iff.rfl

variable (hinv : ∀ c, σ (σ c) = c)
include hinv

/-- The relations satisfied by a unitriangular element. -/
theorem uni_rel {g : SUJ σ} (hg : IsUni (mat g)) :
    mat g 0 1 = -σ (mat g 1 2) ∧ mat g 0 2 + σ (mat g 0 2) + σ (mat g 1 2) * mat g 1 2 = 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hg
  have h := mat_spec g
  have e12 := congrFun (congrFun h 1) 2
  have e22 := congrFun (congrFun h 2) 2
  simp [conjTr, Jm, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6] at e12 e22
  refine ⟨?_, by linear_combination e22⟩
  have := congrArg σ e12
  rw [map_add, hinv, map_zero] at this
  linear_combination this

theorem eq_one_of_isUni {g : SUJ σ} (hg : IsUni (mat g)) (h12 : mat g 1 2 = 0)
    (h02 : mat g 0 2 = 0) : g = 1 := by
  obtain ⟨h01, -⟩ := uni_rel hinv hg
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hg
  rw [h12, map_zero, neg_zero] at h01
  apply mat_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [*]

omit hinv in
theorem isUni_uM (z y : K) : IsUni (uM σ z y) := by simp [IsUni, uM]

variable (σ) in
/-- `PSU₃` in the `J`-model. -/
abbrev PG := StatedProj (SUJ σ)

/-- The unipotent subgroup of `PSU₃`. -/
def Ug : Subgroup (PG σ) := (UJ σ).map (QuotientGroup.mk' _)

/-- The torus of `PSU₃`. -/
noncomputable def Tg : Subgroup (PG σ) := ((QuotientGroup.mk' _).comp (tHom hinv)).range

omit hinv in
theorem mem_Ug {x : PG σ} : x ∈ Ug ↔ ∃ g : SUJ σ, IsUni (mat g) ∧ (g : PG σ) = x := by
  simp [Ug, mem_UJ]

theorem mem_Tg {x : PG σ} : x ∈ Tg hinv ↔ ∃ l : Kˣ, ((tHom hinv l : SUJ σ) : PG σ) = x := Iff.rfl

/-- The Weyl element of `PSU₃`. -/
noncomputable def ng : PG σ := ((nJ hinv : SUJ σ) : PG σ)

theorem isUni_tconj (l : Kˣ) {M : Matrix (Fin 3) (Fin 3) K} (hM : IsUni M) :
    IsUni (tM σ l * M * tM σ l⁻¹) := by
  have h1 : (l : K) ≠ 0 := l.ne_zero
  have h2 : σ (l : K) ≠ 0 := (map_ne_zero σ).2 h1
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [tM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, map_inv₀, *] <;> field_simp

theorem hTU : ∀ t ∈ Tg hinv, ∀ u ∈ (Ug : Subgroup (PG σ)), t * u * t⁻¹ ∈ Ug := by
  rintro _ ⟨l, rfl⟩ x hx
  obtain ⟨g, hg, rfl⟩ := mem_Ug.1 hx
  refine mem_Ug.2 ⟨tHom hinv l * g * tHom hinv l⁻¹, ?_, ?_⟩
  · rw [mat_mul, mat_mul, mat_tHom, mat_tHom]; exact isUni_tconj hinv l hg
  · simp [map_inv]

theorem hUT : ∀ u ∈ (Ug : Subgroup (PG σ)), u ∈ Tg hinv → u = 1 := by
  intro x hx ht
  obtain ⟨g, hg, rfl⟩ := mem_Ug.1 hx
  obtain ⟨l, hl⟩ := (mem_Tg hinv).1 ht
  obtain ⟨c, -, h⟩ := exists_scalar_of_mk_eq hl
  have h12 := h 1 2
  have h02 := h 0 2
  simp [tM] at h12 h02
  rw [eq_one_of_isUni hinv hg h12 h02]
  rfl

theorem nJ_mul_nJ : (nJ hinv : SUJ σ) * nJ hinv = 1 := by
  apply mat_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nM, Matrix.mul_apply, Fin.sum_univ_three]

theorem ng_mul_ng : (ng hinv : PG σ) * ng hinv = 1 := by
  rw [ng, ← QuotientGroup.mk_mul, nJ_mul_nJ, QuotientGroup.mk_one]

theorem mat_tHom_mul_20 (l : Kˣ) {M : Matrix (Fin 3) (Fin 3) K} (hM : IsUni M) :
    (tM σ l * M) 2 0 = 0 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hM
  simp [tM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, *]

theorem ng_not_mem : ng hinv ∉ borelOf (Ug : Subgroup (PG σ)) (Tg hinv) (hTU hinv) := by
  rintro ⟨_, ⟨l, rfl⟩, x, hx, h⟩
  obtain ⟨g, hg, rfl⟩ := mem_Ug.1 hx
  have h' : ((tHom hinv l * g : SUJ σ) : PG σ) = ((nJ hinv : SUJ σ) : PG σ) := by
    rw [QuotientGroup.mk_mul]; exact h.symm
  obtain ⟨c, hc, h⟩ := exists_scalar_of_mk_eq h'
  have h20 := h 2 0
  rw [mat_mul, mat_tHom, mat_tHom_mul_20 hinv l hg, zero_mul] at h20
  simp [nM] at h20

theorem hV : ∀ u ∈ (Ug : Subgroup (PG σ)), ng hinv * u * ng hinv ∈
    borelOf (Ug : Subgroup (PG σ)) (Tg hinv) (hTU hinv) → u = 1 := by
  intro x hx hB
  obtain ⟨g, hg, rfl⟩ := mem_Ug.1 hx
  obtain ⟨_, ⟨l, rfl⟩, y, hy, h⟩ := hB
  obtain ⟨g', hg', rfl⟩ := mem_Ug.1 hy
  have h' : ((tHom hinv l * g' : SUJ σ) : PG σ) = ((nJ hinv * g * nJ hinv : SUJ σ) : PG σ) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h.symm
  obtain ⟨c, hc, h⟩ := exists_scalar_of_mk_eq h'
  have h20 := h 2 0
  rw [mat_mul (tHom hinv l), mat_tHom, mat_tHom_mul_20 hinv l hg', zero_mul] at h20
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hg
  simp [nM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, a1, a2, a3, a4,
    a5, a6] at h20
  -- h20 : the `(0,2)` entry of `g` vanishes
  obtain ⟨-, hrel⟩ := uni_rel hinv ⟨a1, a2, a3, a4, a5, a6⟩
  rw [h20, map_zero, zero_add, zero_add] at hrel
  have h12 : mat g 1 2 = 0 := by
    rcases mul_eq_zero.1 hrel with h | h
    · exact (map_eq_zero σ).1 h
    · exact h
  rw [eq_one_of_isUni hinv ⟨a1, a2, a3, a4, a5, a6⟩ h12 h20]
  rfl

end Groups

section Bruhat

variable {σ} (hinv : ∀ c, σ (σ c) = c)
include hinv

omit hinv in
theorem herm_entry (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (conjTr σ M * Jm * M : Matrix (Fin 3) (Fin 3) K) i j =
      σ (M 2 i) * M 0 j + σ (M 1 i) * M 1 j + σ (M 0 i) * M 2 j := by
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Jm, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

omit hinv in
theorem key_entry (g : SUJ σ) (i j : Fin 3) :
    σ (mat g 2 i) * mat g 0 j + σ (mat g 1 i) * mat g 1 j + σ (mat g 0 i) * mat g 2 j = Jm i j := by
  rw [← herm_entry, mat_spec]

/-- An element whose first column is a multiple of `e₀` lies in `TU`. -/
theorem mem_borel_of_entry (g : SUJ σ) (h20 : mat g 2 0 = 0) :
    (g : PG σ) ∈ borelOf (Ug : Subgroup (PG σ)) (Tg hinv) (hTU hinv) := by
  have e00 := key_entry g 0 0
  have e01 := key_entry g 0 1
  have e02 := key_entry g 0 2
  have j00 : (Jm : Matrix (Fin 3) (Fin 3) K) 0 0 = 0 := by simp [Jm]
  have j01 : (Jm : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by simp [Jm]
  have j02 : (Jm : Matrix (Fin 3) (Fin 3) K) 0 2 = 1 := by simp [Jm]
  simp only [h20, map_zero, zero_mul, mul_zero, add_zero, zero_add, j00] at e00
  have h10 : mat g 1 0 = 0 := by
    rcases mul_eq_zero.1 e00 with h | h
    · exact (map_eq_zero σ).1 h
    · exact h
  simp only [h20, h10, map_zero, zero_mul, mul_zero, add_zero, zero_add, j01] at e01
  simp only [h20, h10, map_zero, zero_mul, mul_zero, add_zero, zero_add, j02] at e02
  have hdet := mat_det g
  rw [det_fin_three, h10, h20] at hdet
  have h00 : mat g 0 0 ≠ 0 := by
    intro h; rw [h] at hdet; simp at hdet
  have hσ00 : σ (mat g 0 0) ≠ 0 := (map_ne_zero σ).2 h00
  have h21 : mat g 2 1 = 0 := by
    rcases mul_eq_zero.1 e01 with h | h
    · exact absurd h hσ00
    · exact h
  rw [h21] at hdet
  simp only [mul_zero, zero_mul, sub_zero, add_zero] at hdet
  -- `hdet : g₀₀ g₁₁ g₂₂ = 1`, `e02 : σ(g₀₀) g₂₂ = 1`
  let l : Kˣ := Units.mk0 _ h00
  refine ⟨_, ⟨l, rfl⟩, ((tHom hinv l⁻¹ * g : SUJ σ) : PG σ), mem_Ug.2 ⟨_, ?_, rfl⟩, ?_⟩
  · have h11 : mat g 1 1 = σ (mat g 0 0) / mat g 0 0 := by
      field_simp
      linear_combination σ (mat g 0 0) * hdet - mat g 0 0 * mat g 1 1 * e02
    rw [mat_mul, mat_tHom]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [tM, l, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, map_inv₀,
        h10, h20, h21, h11]
    all_goals first
      | (field_simp; done)
      | (field_simp; linear_combination e02)
      | linear_combination e02
  · change _ = ((tHom hinv l : SUJ σ) : PG σ) * _
    rw [← QuotientGroup.mk_mul, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem hcover (g : PG σ) : g ∈ borelOf (Ug : Subgroup (PG σ)) (Tg hinv) (hTU hinv) ∨
    ∃ u ∈ (Ug : Subgroup (PG σ)), ∃ t ∈ Tg hinv, ∃ u' ∈ (Ug : Subgroup (PG σ)),
      g = u * ng hinv * t * u' := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  by_cases h20 : mat g 2 0 = 0
  · exact Or.inl (mem_borel_of_entry hinv g h20)
  right
  have e00 := key_entry g 0 0
  simp only [Jm] at e00
  simp at e00
  have hσ20 : σ (mat g 2 0) ≠ 0 := (map_ne_zero σ).2 h20
  set z := mat g 1 0 / mat g 2 0 with hz
  set y := mat g 0 0 / mat g 2 0 with hy
  have hzy : y + σ y + σ z * z = 0 := by
    rw [hz, hy, map_div₀, map_div₀]
    field_simp
    first | linear_combination e00 | linear_combination -e00
  have hzy' : σ y + σ (σ y) + σ (-z) * (-z) = 0 := by
    rw [hinv, map_neg]; linear_combination hzy
  set u := uJ hinv z y hzy
  set v := uJ hinv (-z) (σ y) hzy'
  have huv : u * v = 1 := by
    apply mat_ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, v, uM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, hinv] <;>
      linear_combination hzy
  set h := nJ hinv * v * g
  have hh : mat h 2 0 = 0 := by
    simp only [h, mat_mul, mat_nJ, v, mat_uJ]
    simp [nM, uM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, hinv]
    rw [hz, hy, map_div₀, map_div₀]
    field_simp
    first | linear_combination e00 | linear_combination -e00
  obtain ⟨_, ⟨l, rfl⟩, x, hx, hxe⟩ := mem_borel_of_entry hinv h hh
  refine ⟨u, mem_Ug.2 ⟨u, isUni_uM z y, rfl⟩, _, ⟨l, rfl⟩, x, hx, ?_⟩
  have hg : g = u * nJ hinv * h := by
    simp only [h, ← mul_assoc]
    rw [mul_assoc u, nJ_mul_nJ, mul_one, huv, one_mul]
  rw [mul_assoc _ _ x, ← hxe, hg, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  rfl

/-- **`T n ⊆ UnUnU`.** -/
theorem hTn (hσ : IsUnitaryInvolution σ) : ∀ t ∈ Tg hinv, ∃ a ∈ (Ug : Subgroup (PG σ)),
    ∃ b ∈ (Ug : Subgroup (PG σ)), ∃ c ∈ (Ug : Subgroup (PG σ)),
      t * ng hinv = a * ng hinv * b * ng hinv * c := by
  rintro _ ⟨l, rfl⟩
  have hl : (l : K) ≠ 0 := l.ne_zero
  have hσl : σ (l : K) ≠ 0 := (map_ne_zero σ).2 hl
  have hN : σ (-((l : K) + σ l) / (l * σ l)) = -((l : K) + σ l) / (l * σ l) := by
    rw [map_div₀, map_neg, map_add, map_mul, hinv]; ring
  obtain ⟨z, hz⟩ := hσ.exists_norm hN
  have hR : σ z * z * l * σ l + l + σ l = 0 := by rw [hz]; field_simp; ring
  have c1 : (l : K) + σ l + σ (z * σ l) * (z * σ l) = 0 := by
    rw [map_mul, hinv]; linear_combination hR
  have c2 : (σ l)⁻¹ + σ ((σ l)⁻¹) + σ z * z = 0 := by
    rw [map_inv₀, hinv]; field_simp
    first | linear_combination hR | linear_combination -hR
  have c3 : (l : K) + σ l + σ (z * l) * (z * l) = 0 := by
    rw [map_mul]; linear_combination hR
  refine ⟨_, mem_Ug.2 ⟨uJ hinv (z * σ l) l c1, isUni_uM _ _, rfl⟩,
    _, mem_Ug.2 ⟨uJ hinv z (σ l)⁻¹ c2, isUni_uM _ _, rfl⟩,
    _, mem_Ug.2 ⟨uJ hinv (z * l) l c3, isUni_uM _ _, rfl⟩, ?_⟩
  have key : tHom hinv l * nJ hinv = uJ hinv (z * σ l) l c1 * nJ hinv * uJ hinv z (σ l)⁻¹ c2 *
      nJ hinv * uJ hinv (z * l) l c3 := by
    apply mat_ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uM, tM, nM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, hinv,
        map_mul, map_inv₀]
    all_goals first
      | (field_simp; done)
      | ring1
      | (field_simp; ring1)
      | linear_combination (norm := (field_simp; ring1)) (σ (l : K))⁻¹ * hR
      | linear_combination (norm := (field_simp; ring1)) -(σ (l : K))⁻¹ * hR
      | linear_combination (norm := (field_simp; ring1)) σ z * hR
      | linear_combination (norm := (field_simp; ring1)) -σ z * hR
      | linear_combination (norm := (field_simp; ring1)) (l : K) / σ l * hR
      | linear_combination (norm := (field_simp; ring1)) -(l : K) / σ l * hR
      | linear_combination (norm := (field_simp; ring1)) (l : K)⁻¹ * hR
      | linear_combination (norm := (field_simp; ring1)) -(l : K)⁻¹ * hR
      | linear_combination (norm := (field_simp; ring1)) z * hR
      | linear_combination (norm := (field_simp; ring1)) -z * hR
  change ((tHom hinv l : SUJ σ) : PG σ) * ((nJ hinv : SUJ σ) : PG σ) = _
  rw [← QuotientGroup.mk_mul, key]
  rfl

end Bruhat

section Cards

variable {σ} (hinv : ∀ c, σ (σ c) = c)
include hinv

theorem isCyclic_Tg [Finite K] : IsCyclic (Tg hinv : Subgroup (PG σ)) :=
  isCyclic_of_surjective _ ((QuotientGroup.mk' _).comp (tHom hinv)).rangeRestrict_surjective

theorem even_card_Tg [Finite K] (h2 : (2 : K) ≠ 0) : Even (Nat.card (Tg hinv : Subgroup (PG σ))) := by
  let τ : Tg hinv := ⟨_, ⟨-1, rfl⟩⟩
  have hτ : orderOf τ = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change (((QuotientGroup.mk' _).comp (tHom hinv)) (-1)) ^ 2 = 1
      rw [← map_pow, neg_one_sq, map_one]
    · intro h
      have h' : ((tHom hinv (-1) : SUJ σ) : PG σ) = ((1 : SUJ σ) : PG σ) :=
        congrArg Subtype.val h
      obtain ⟨c, -, h⟩ := exists_scalar_of_mk_eq h'.symm
      have h00 := h 0 0
      have h11 := h 1 1
      simp [tM] at h00 h11
      apply h2
      linear_combination h11 - h00
  have := orderOf_dvd_natCard τ
  rw [hτ] at this
  exact (even_iff_two_dvd).2 this

theorem odd_card_Ug [Finite K] (h2 : (2 : K) ≠ 0) : Odd (Nat.card (Ug : Subgroup (PG σ))) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  obtain ⟨g, hg, hgx⟩ := mem_Ug.1 x.2
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hgg : ((g * g : SUJ σ) : PG σ) = ((1 : SUJ σ) : PG σ) := by
    rw [QuotientGroup.mk_mul, hgx, ← sq]
    exact congrArg Subtype.val hx2
  obtain ⟨c, -, h⟩ := exists_scalar_of_mk_eq hgg
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hg
  have s00 : mat (g * g) 0 0 = 1 := by
    rw [mat_mul]; simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6]
  have s01 : mat (g * g) 0 1 = 2 * mat g 0 1 := by
    rw [mat_mul]; simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6]; ring
  have s12 : mat (g * g) 1 2 = 2 * mat g 1 2 := by
    rw [mat_mul]; simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6]; ring
  have s02 : mat (g * g) 0 2 = 2 * mat g 0 2 + mat g 0 1 * mat g 1 2 := by
    rw [mat_mul]; simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6]; ring
  have h00 := h 0 0
  rw [s00, mat_one, Matrix.one_apply_eq, one_mul] at h00
  subst h00
  have h01 := h 0 1
  rw [s01, mat_one, Matrix.one_apply_ne (by decide), mul_one] at h01
  have h12 := h 1 2
  rw [s12, mat_one, Matrix.one_apply_ne (by decide), mul_one] at h12
  have h02 := h 0 2
  rw [s02, mat_one, Matrix.one_apply_ne (by decide), mul_one] at h02
  replace h01 := mul_eq_zero.1 h01.symm
  replace h12 := mul_eq_zero.1 h12.symm
  have e01 : mat g 0 1 = 0 := by
    rcases h01 with h | h
    · exact absurd h h2
    · exact h
  have e12 : mat g 1 2 = 0 := by
    rcases h12 with h | h
    · exact absurd h h2
    · exact h
  have e02 : mat g 0 2 = 0 := by
    rw [e01, zero_mul, add_zero] at h02
    rcases mul_eq_zero.1 h02.symm with h | h
    · exact absurd h h2
    · exact h
  have hg1 := eq_one_of_isUni hinv ⟨a1, a2, a3, a4, a5, a6⟩ e12 e02
  have : x = 1 := Subtype.ext (by rw [← hgx, hg1]; rfl)
  rw [this, orderOf_one] at hx
  omega

theorem even_card_Ug [Finite K] (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0) :
    Even (Nat.card (Ug : Subgroup (PG σ))) := by
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hc : τ + σ τ + σ 0 * 0 = 0 := by rw [mul_zero, add_zero]; exact hτ
  let v : (Ug : Subgroup (PG σ)) := ⟨_, mem_Ug.2 ⟨uJ hinv 0 τ hc, isUni_uM _ _, rfl⟩⟩
  have hv : orderOf v = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change ((uJ hinv 0 τ hc : SUJ σ) : PG σ) ^ 2 = ((1 : SUJ σ) : PG σ)
      rw [sq, ← QuotientGroup.mk_mul]
      congr 1
      apply mat_ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [uM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
      linear_combination τ * h2
    · intro h
      have h' : ((uJ hinv 0 τ hc : SUJ σ) : PG σ) = ((1 : SUJ σ) : PG σ) := congrArg Subtype.val h
      obtain ⟨c, hc, h⟩ := exists_scalar_of_mk_eq h'.symm
      have h02 := h 0 2
      rw [mat_one, Matrix.one_apply_ne (by decide)] at h02
      exact hτ0 (by simpa [uM] using h02)
  have := orderOf_dvd_natCard v
  rw [hv] at this
  exact (even_iff_two_dvd).2 this

end Cards

section Main

variable {σ}

/-- **Hall–Paige for `PSU₃(q)`, `q` odd** (in the `J`-model). -/
theorem hasCompleteMapping_PG [Finite K] (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) ≠ 0) :
    HasCompleteMapping (PG σ) :=
  hasCompleteMapping_of_rankOne_split (U := Ug) (T := Tg hσ.invol) (hTU := hTU hσ.invol)
    (ng hσ.invol) (odd_card_Ug hσ.invol h2) (ng_mul_ng hσ.invol) (hUT hσ.invol)
    (ng_not_mem hσ.invol) (hV hσ.invol) (hcover hσ.invol) (hTn hσ.invol hσ)
    (isCyclic_Tg hσ.invol) (even_card_Tg hσ.invol h2)

/-- **`PSU₃(q)`, `q` even** (in the `J`-model): the Wilcox criterion with `H = TU`. -/
theorem wilcoxCriterion_PG [Finite K] (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (hG : IsGood (PG σ)) : WilcoxCriterion (PG σ) :=
  wilcoxCriterion_of_rankOne_split_even (U := Ug) (T := Tg hσ.invol) (hTU := hTU hσ.invol) hG
    (ng hσ.invol) (even_card_Ug hσ.invol hσ h2) (ng_mul_ng hσ.invol) (hUT hσ.invol)
    (ng_not_mem hσ.invol) (hV hσ.invol) (hcover hσ.invol)

end Main

end CFSGOutside.HallPaige.UnitaryThree
