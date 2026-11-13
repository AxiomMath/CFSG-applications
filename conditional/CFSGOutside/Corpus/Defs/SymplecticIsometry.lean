import Mathlib

/-!
# Copied corpus definitions: the isometry group of a bilinear form, and symplectic transvections

Copied verbatim at AxiomMath/CFSG commit 69cb972f587a3ecc035e092253167ff2e303c962, under `CFSGOutside.Corpus`:
* `bilinIsometryGroup` and `mem_bilinIsometryGroup` from `CFSG/LocalAnalysis/ComponentInitial/LinearIsometry.lean`
  (lines 18, 30);
* `symplecticTransvection` and `symplecticTransvection_apply` from
  `CFSG/ClassicalGroups/Alternating/Transvections.lean` (lines 41, 49).
-/

namespace CFSGOutside.Corpus.LocalAnalysis.ComponentInitial

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Copy of `CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup`. -/
def bilinIsometryGroup (B : LinearMap.BilinForm R M) :
    Subgroup (LinearMap.GeneralLinearGroup R M) where
  carrier := {g | ∀ x y, B ((g : M →ₗ[R] M) x) ((g : M →ₗ[R] M) y) = B x y}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h := hg (((g⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) x)
      (((g⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) y)
    simp only [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply] at h
    exact h.symm

theorem mem_bilinIsometryGroup {B : LinearMap.BilinForm R M}
    {g : LinearMap.GeneralLinearGroup R M} :
    g ∈ bilinIsometryGroup B ↔ ∀ x y, B ((g : M →ₗ[R] M) x) ((g : M →ₗ[R] M) y) = B x y :=
  Iff.rfl

end CFSGOutside.Corpus.LocalAnalysis.ComponentInitial

namespace CFSGOutside.Corpus.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Copy of `CFSG.ClassicalGroups.Alternating.symplecticTransvection`: `x ↦ x + c B(x, a) a`. -/
def symplecticTransvection (B : BilinForm K V) (hB : B.IsAlt) (a : V) (c : K) :
    LinearMap.GeneralLinearGroup K V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.transvection (f := c • B.flip a) (v := a)
      (show c • B a a = 0 by rw [hB.self_eq_zero, smul_zero]))

theorem symplecticTransvection_apply {B : BilinForm K V} (hB : B.IsAlt) (a : V) (c : K) (x : V) :
    (symplecticTransvection B hB a c : V →ₗ[K] V) x = x + (c * B x a) • a :=
  rfl

end CFSGOutside.Corpus.ClassicalGroups.Alternating
