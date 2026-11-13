import CFSGOutside.HallPaige.Lie.UnitaryElements
import CFSGOutside.HallPaige.Lie.Polar
import CFSGOutside.Corpus.HallPaige.LieSymplectic
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The projective special unitary groups acting on isotropic points

`PSU_n(K)` acts on the isotropic points of `ℙ(Kⁿ)` for the standard hermitian form. We verify the
hypotheses of the polar-space criterion `CFSGOutside.HallPaige.wilcoxCriterion_of_polar` for `n ≥ 4`, except
the goodness of the point stabilizer: transitivity on isotropic points and transitivity of the
point stabilizer on the perpendicular and on the non-perpendicular isotropic points, using
unitary transvections and Eichler transformations.

The isotropic-point machinery (`IsIsoPt`, `isoPts`, `pt`, …) is ported from AxiomMath/CFSG
@ 69cb972, CFSG/ClassicalGroups/Unitary/Action.lean.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix MulAction Corpus.Lie
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

section IsoPts

variable (σ) in
/-- An isotropic point. -/
def IsIsoPt (x : ℙ K (Fin n → K)) : Prop := herm σ x.rep x.rep = 0

theorem isIsoPt_mk {v : Fin n → K} (hv : v ≠ 0) :
    IsIsoPt σ (Projectivization.mk K v hv) ↔ herm σ v v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [IsIsoPt, ← ha, Units.smul_def, herm_smul_left, herm_smul_right]
  have h0 : σ (a : K) ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  constructor
  · intro h
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h0)).resolve_left a.ne_zero
  · intro h
    rw [h, mul_zero, mul_zero]

variable (σ n) in
/-- The isotropic points, as a sub-action of `SU`. -/
def isoPts : SubMulAction (SUid σ n) (ℙ K (Fin n → K)) where
  carrier := {x | IsIsoPt σ x}
  smul_mem' g x hx := by
    induction x using Projectivization.ind with
    | h v hv =>
      change IsIsoPt σ (Projectivization.mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv))
      rw [isIsoPt_mk, herm_smul_smul]
      exact (isIsoPt_mk hv).mp hx

/-- The isotropic point spanned by an isotropic vector. -/
def pt (v : Fin n → K) (hv : v ≠ 0) (hiso : herm σ v v = 0) : isoPts σ n :=
  ⟨Projectivization.mk K v hv, (isIsoPt_mk hv).mpr hiso⟩

theorem isoPts_ind {P : isoPts σ n → Prop}
    (h : ∀ (v : Fin n → K) (hv : v ≠ 0) (hiso : herm σ v v = 0), P (pt v hv hiso)) :
    ∀ x, P x := by
  rintro ⟨x, hx⟩
  induction x using Projectivization.ind with
  | h v hv => exact h v hv ((isIsoPt_mk hv).mp hx)

theorem smul_pt (g : SUid σ n) {v : Fin n → K} (hv : v ≠ 0) (hiso : herm σ v v = 0) :
    g • pt v hv hiso = pt (g • v) ((smul_ne_zero_iff_ne g).mpr hv)
      (by rw [herm_smul_smul]; exact hiso) :=
  rfl

theorem pt_eq_pt_iff {v w : Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) (hv' : herm σ v v = 0)
    (hw' : herm σ w w = 0) : pt v hv hv' = pt w hw hw' ↔ ∃ c : K, c • w = v := by
  rw [← Projectivization.mk_eq_mk_iff' K v w hv hw]
  exact Subtype.ext_iff

theorem pt_eq_pt_of_smul {v w : Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) (hv' : herm σ v v = 0)
    (hw' : herm σ w w = 0) (c : K) (h : v = c • w) : pt v hv hv' = pt w hw hw' :=
  (pt_eq_pt_iff hv hw hv' hw').mpr ⟨c, h.symm⟩

theorem smul_eq_of_mem_scalars {g : SUid σ n}
    (hg : g ∈ (StatedScalars (Fin n) K).subgroupOf (SUid σ n)) (x : isoPts σ n) : g • x = x := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨u, hu⟩ := hg
  induction x using isoPts_ind with
  | h v hv hiso =>
  rw [smul_pt]
  refine pt_eq_pt_of_smul _ _ _ _ (u : K) ?_
  rw [smul_def, ← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext k
  simp [Matrix.mulVec_diagonal]

/-- Perpendicularity of isotropic points. -/
def perpU (x y : isoPts σ n) : Prop := herm σ (x : ℙ K (Fin n → K)).rep (y : ℙ K (Fin n → K)).rep = 0

theorem perpU_pt {v w : Fin n → K} (hv : v ≠ 0) (hw : w ≠ 0) (hv' : herm σ v v = 0)
    (hw' : herm σ w w = 0) : perpU (pt v hv hv') (pt w hw hw') ↔ herm σ v w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  change herm σ (Projectivization.mk K v hv).rep (Projectivization.mk K w hw).rep = 0 ↔ _
  rw [← ha, ← hb, Units.smul_def, Units.smul_def, herm_smul_left, herm_smul_right]
  have h0 : σ (a : K) ≠ 0 := (map_ne_zero σ).mpr a.ne_zero
  simp [h0, b.ne_zero]

theorem perpU_refl (x : isoPts σ n) : perpU x x := x.2

theorem perpU_smul (g : SUid σ n) (x y : isoPts σ n) : perpU (g • x) (g • y) ↔ perpU x y := by
  induction x using isoPts_ind with
  | h v hv hiso =>
  induction y using isoPts_ind with
  | h w hw hiso' =>
  rw [smul_pt, smul_pt, perpU_pt, perpU_pt, herm_smul_smul]

end IsoPts

section PSU

/-- The action of `PSU` on isotropic points. -/
noncomputable def psuHom : StatedProj (SUid σ n) →* Equiv.Perm (isoPts σ n) :=
  QuotientGroup.lift _ (MulAction.toPermHom (SUid σ n) (isoPts σ n)) (by
    intro g hg
    rw [MonoidHom.mem_ker]
    ext x
    exact congrArg Subtype.val (smul_eq_of_mem_scalars hg x))

noncomputable instance : MulAction (StatedProj (SUid σ n)) (isoPts σ n) :=
  MulAction.compHom _ psuHom

theorem psu_smul (g : SUid σ n) (x : isoPts σ n) :
    (g : StatedProj (SUid σ n)) • x = g • x := rfl

theorem perpU_psu_smul (g : StatedProj (SUid σ n)) (x y : isoPts σ n) :
    perpU (g • x) (g • y) ↔ perpU x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [psu_smul, psu_smul]
  exact perpU_smul g x y

end PSU

end CFSGOutside.HallPaige.Unitary
