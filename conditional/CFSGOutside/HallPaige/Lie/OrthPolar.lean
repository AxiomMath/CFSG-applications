import CFSGOutside.HallPaige.Lie.OrthEichler
import CFSGOutside.HallPaige.Lie.Polar
import CFSGOutside.HallPaige.Sporadic.GoodOfKlein
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# `PΩ(Q)` acting on the singular points

For a quadratic form `Q` on `K^ι` with nondegenerate polar form and a frame of at least three
mutually orthogonal hyperbolic pairs `(e i, f i)`, the group `PΩ(Q) = Ω(Q) / (scalars)` acts on
the singular points of `ℙ(K^ι)` with rank three: the stabilizer of `[e₀]` is transitive on the
singular points `≠ [e₀]` perpendicular to `[e₀]` and on those not perpendicular to it. Only
Eichler transformations are used (`CFSGOutside.HallPaige.Orth.Frame.exists_move`).

The stabilizer of `[e₀]` is good: in characteristic `2` the Eichler transformations
`E(e₀, e₁)`, `E(e₀, f₁)` are commuting involutions; otherwise the squares of the "Weyl elements"
`E(e₀, e_j) E(f_j, -f₀) E(e₀, e_j)` (`-1` on the planes `0` and `j`) for `j = 1, 2` are.

Main result: `CFSGOutside.HallPaige.Orth.wilcoxCriterion_omega`.
-/

namespace CFSGOutside.HallPaige.Orth

open Matrix QuadraticMap Corpus.Lie MulAction
open scoped LinearAlgebra.Projectivization

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

/-! ### Basic moves -/

/-- An Eichler transformation fixing a vector orthogonal to its data. -/
theorem eichGL_smul_fix {a x v : ι → K} (ha : Q a = 0) (hax : polar Q a x = 0)
    (hva : polar Q v a = 0) (hvx : polar Q v x = 0) : eichGL Q a x • v = v := by
  rw [eichGL_smul_eq ha hax, hva, hvx]; simp

/-- **Partner move**: if `a` is singular and `B(a, x) = B(a, x') = 1` for singular `x, x'`,
then `E(a, x' - x)` maps `x` to `x'`. -/
theorem eichGL_smul_partner {a x x' : ι → K} (ha : Q a = 0) (hx : Q x = 0) (hx' : Q x' = 0)
    (hax : polar Q a x = 1) (hax' : polar Q a x' = 1) : eichGL Q a (x' - x) • x = x' := by
  have h0 : polar Q a (x' - x) = 0 := by rw [polar_sub_right, hax, hax', sub_self]
  have hQ : Q (x' - x) = -polar Q x x' := by
    rw [sub_eq_add_neg, map_add_eq, QuadraticMap.map_neg, hx, hx', polar_neg_right,
      polar_comm _ x' x]
    ring
  rw [eichGL_smul_eq ha h0, polar_comm _ x a, hax, hQ, polar_sub_right,
    polar_self_of_singular hx]
  module

theorem map_sub_eq (x y : ι → K) : Q (x - y) = Q x + Q y - polar Q x y := by
  rw [sub_eq_add_neg, map_add_eq, QuadraticMap.map_neg, polar_neg_right]; ring

theorem map_smul_eq (c : K) (x : ι → K) : Q (c • x) = c * c * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul]

namespace Frame

variable {m : ℕ} (F : Frame Q m)

/-- `v` is orthogonal to the hyperbolic planes indexed by `J`. -/
def Perp (J : Finset (Fin m)) (v : ι → K) : Prop :=
  ∀ j ∈ J, polar Q v (F.e j) = 0 ∧ polar Q v (F.f j) = 0

theorem perp_e {J : Finset (Fin m)} {i : Fin m} (hi : i ∉ J) : F.Perp J (F.e i) := fun j hj =>
  ⟨F.ee i j, F.ef_ne (fun h => hi (h ▸ hj))⟩

theorem perp_f {J : Finset (Fin m)} {i : Fin m} (hi : i ∉ J) : F.Perp J (F.f i) := fun j hj =>
  ⟨F.fe_ne (fun h => hi (h ▸ hj)), F.ff i j⟩

theorem Perp.add {J : Finset (Fin m)} {v w : ι → K} (hv : F.Perp J v) (hw : F.Perp J w) :
    F.Perp J (v + w) := fun j hj => by
  rw [polar_add_left, polar_add_left, (hv j hj).1, (hv j hj).2, (hw j hj).1, (hw j hj).2]
  simp

theorem Perp.sub {J : Finset (Fin m)} {v w : ι → K} (hv : F.Perp J v) (hw : F.Perp J w) :
    F.Perp J (v - w) := fun j hj => by
  rw [polar_sub_left, polar_sub_left, (hv j hj).1, (hv j hj).2, (hw j hj).1, (hw j hj).2]
  simp

theorem Perp.smul {J : Finset (Fin m)} {v : ι → K} (hv : F.Perp J v) (c : K) :
    F.Perp J (c • v) := fun j hj => by
  rw [polar_smul_left, polar_smul_left, (hv j hj).1, (hv j hj).2]
  simp

/-- An Eichler transformation with data orthogonal to the planes `J` fixes the `e j`, `j ∈ J`. -/
theorem eichGL_fix_e {J : Finset (Fin m)} {a x : ι → K} (ha : Q a = 0) (hax : polar Q a x = 0)
    (haJ : F.Perp J a) (hxJ : F.Perp J x) {j : Fin m} (hj : j ∈ J) :
    eichGL Q a x • F.e j = F.e j :=
  eichGL_smul_fix ha hax (by rw [polar_comm]; exact (haJ j hj).1)
    (by rw [polar_comm]; exact (hxJ j hj).1)

/-- Moving `e i` to a singular `x` with `B(f i, x) = 1`. -/
theorem move_f (hm : 3 ≤ m) {J : Finset (Fin m)} {i : Fin m} (hi : i ∉ J) {x : ι → K}
    (hQx : Q x = 0) (hxJ : F.Perp J x) (hfx : polar Q (F.f i) x = 1) :
    eichGL Q (F.f i) (x - F.e i) ∈ StatedOmega ⇑Q ∧
      (∀ j ∈ J, eichGL Q (F.f i) (x - F.e i) • F.e j = F.e j) ∧
      eichGL Q (F.f i) (x - F.e i) • F.e i = x := by
  have h0 : polar Q (F.f i) (x - F.e i) = 0 := by
    rw [polar_sub_right, hfx, F.fe_self, sub_self]
  exact ⟨F.eichGL_mem_f hm i h0, fun j hj => F.eichGL_fix_e (F.qf i) h0 (F.perp_f hi)
    (hxJ.sub F (F.perp_e hi)) hj, eichGL_smul_partner (F.qf i) (F.qe i) hQx (F.fe_self i) hfx⟩

/-- Moving a singular `x` with `B(e i, x) = 1` to another such `x'`. -/
theorem move_e (hm : 3 ≤ m) {J : Finset (Fin m)} {i : Fin m} (hi : i ∉ J) {x x' : ι → K}
    (hQx : Q x = 0) (hQx' : Q x' = 0) (hxJ : F.Perp J x) (hxJ' : F.Perp J x')
    (hex : polar Q (F.e i) x = 1) (hex' : polar Q (F.e i) x' = 1) :
    eichGL Q (F.e i) (x' - x) ∈ StatedOmega ⇑Q ∧
      (∀ j ∈ J, eichGL Q (F.e i) (x' - x) • F.e j = F.e j) ∧
      eichGL Q (F.e i) (x' - x) • x = x' := by
  have h0 : polar Q (F.e i) (x' - x) = 0 := by rw [polar_sub_right, hex, hex', sub_self]
  exact ⟨F.eichGL_mem hm i h0, fun j hj => F.eichGL_fix_e (F.qe i) h0 (F.perp_e hi)
    (hxJ'.sub F hxJ) hj, eichGL_smul_partner (F.qe i) hQx hQx' hex hex'⟩

/-- Case of `exists_move` where `B(y, f i) ≠ 0`. -/
theorem exists_move_of_f (hm : 3 ≤ m) {J : Finset (Fin m)} {i : Fin m} (hi : i ∉ J)
    {y : ι → K} (hQy : Q y = 0) (hyJ : F.Perp J y) (hyf : polar Q y (F.f i) ≠ 0) :
    ∃ g ∈ StatedOmega ⇑Q, (∀ j ∈ J, g • F.e j = F.e j) ∧ ∃ c : K, c ≠ 0 ∧ g • F.e i = c • y := by
  set c := (polar Q y (F.f i))⁻¹
  have h1 : polar Q (F.f i) (c • y) = 1 := by
    rw [polar_smul_right, polar_comm, smul_eq_mul, inv_mul_cancel₀ hyf]
  obtain ⟨hg, hfix, hmove⟩ := F.move_f hm hi (by rw [map_smul_eq, hQy, mul_zero])
    (hyJ.smul F c) h1
  exact ⟨_, hg, hfix, c, inv_ne_zero hyf, hmove⟩

/-- **Transitivity on singular vectors up to scalars**, inside the orthogonal complement of the
planes `J`, by elements of `Ω` fixing the `e j`, `j ∈ J`. -/
theorem exists_move (hm : 3 ≤ m) (hnd : ∀ y : ι → K, y ≠ 0 → ∃ w, polar Q y w ≠ 0)
    {J : Finset (Fin m)} {i k : Fin m} (hi : i ∉ J) (hk : k ∉ J) (hik : i ≠ k)
    {y : ι → K} (hy0 : y ≠ 0) (hQy : Q y = 0) (hyJ : F.Perp J y) :
    ∃ g ∈ StatedOmega ⇑Q, (∀ j ∈ J, g • F.e j = F.e j) ∧ ∃ c : K, c ≠ 0 ∧ g • F.e i = c • y := by
  by_cases h1 : polar Q y (F.f i) ≠ 0
  · exact F.exists_move_of_f hm hi hQy hyJ h1
  push Not at h1
  by_cases h2 : polar Q y (F.e i) ≠ 0
  · -- through `x₀ = e i + f i + e k - f k`
    set x₀ := (F.e i + F.f i) + (F.e k - F.f k)
    have hki : k ≠ i := Ne.symm hik
    have hx₀f : polar Q (F.f i) x₀ = 1 := by
      simp only [x₀, polar_add_right, polar_sub_right, F.fe_self, F.ff, F.fe_ne hik]; ring
    have hx₀e : polar Q (F.e i) x₀ = 1 := by
      simp only [x₀, polar_add_right, polar_sub_right, F.ef_self, F.ee, F.ef_ne hik]; ring
    have hQx₀ : Q x₀ = 0 := by
      simp only [x₀, map_add_eq, map_sub_eq, polar_add_left, polar_add_right, polar_sub_left,
        polar_sub_right, F.qe, F.qf, F.ef_self, F.ee, F.ff, F.ef_ne hik, F.fe_ne hik,
        F.ef_ne hki, F.fe_ne hki]
      ring
    have hx₀J : F.Perp J x₀ :=
      ((F.perp_e hi).add F (F.perp_f hi)).add F ((F.perp_e hk).sub F (F.perp_f hk))
    set c := (polar Q (F.e i) y)⁻¹
    have hc : c ≠ 0 := inv_ne_zero (by rw [polar_comm]; exact h2)
    have hcy : polar Q (F.e i) (c • y) = 1 := by
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ (by rw [polar_comm]; exact h2)]
    obtain ⟨hg₁, hfix₁, hmove₁⟩ := F.move_f hm hi hQx₀ hx₀J hx₀f
    obtain ⟨hg₂, hfix₂, hmove₂⟩ := F.move_e hm hi hQx₀ (by rw [map_smul_eq, hQy, mul_zero])
      hx₀J (hyJ.smul F c) hx₀e hcy
    refine ⟨_, mul_mem hg₂ hg₁, fun j hj => by rw [mul_smul, hfix₁ j hj, hfix₂ j hj], c, hc, ?_⟩
    rw [mul_smul, hmove₁, hmove₂]
  push Not at h2
  -- `y` is orthogonal to the plane `i`: first move it off that plane
  have hyJi : F.Perp (insert i J) y := fun j hj => by
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact ⟨h2, h1⟩
    · exact hyJ j hj
  obtain ⟨w, hw⟩ := hnd y hy0
  set w' := F.rest (insert i J) w
  have hw' : polar Q y w' ≠ 0 := by rw [F.polar_rest_right _ _ hyJi]; exact hw
  set w'' := (polar Q y w')⁻¹ • w'
  have hyw'' : polar Q y w'' = 1 := by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hw']
  have hw''J : F.Perp (insert i J) w'' := fun j hj => by
    rw [polar_smul_left, polar_smul_left, F.polar_rest_e _ _ hj, F.polar_rest_f _ _ hj]
    simp
  have hew'' : polar Q (F.e i) w'' = 0 := by
    rw [polar_comm]; exact (hw''J i (Finset.mem_insert_self _ _)).1
  have hw''J' : F.Perp J w'' := fun j hj => hw''J j (Finset.mem_insert_of_mem hj)
  have hg₀ : eichGL Q (F.e i) w'' ∈ StatedOmega ⇑Q := F.eichGL_mem hm i hew''
  have hfix₀ : ∀ j ∈ J, eichGL Q (F.e i) w'' • F.e j = F.e j := fun j hj =>
    F.eichGL_fix_e (F.qe i) hew'' (F.perp_e hi) hw''J' hj
  set y₃ := y - F.e i
  have hy₃ : eichGL Q (F.e i) w'' • y = y₃ := by
    rw [eichGL_smul_eq (F.qe i) hew'', h2, hyw'']; simp [y₃]
  have hQy₃ : Q y₃ = 0 := by rw [map_sub_eq, hQy, F.qe, h2]; ring
  have hy₃J : F.Perp J y₃ := hyJ.sub F (F.perp_e hi)
  have hy₃f : polar Q y₃ (F.f i) ≠ 0 := by
    rw [polar_sub_left, h1, F.ef_self]; norm_num
  obtain ⟨g₃, hg₃, hfix₃, c, hc, hmove₃⟩ := F.exists_move_of_f hm hi hQy₃ hy₃J hy₃f
  refine ⟨(eichGL Q (F.e i) w'')⁻¹ * g₃, mul_mem (inv_mem hg₀) hg₃, fun j hj => ?_, c, hc, ?_⟩
  · rw [mul_smul, hfix₃ j hj, inv_smul_eq_iff, hfix₀ j hj]
  · rw [mul_smul, hmove₃, gl_smul_smul, ← hy₃, inv_smul_smul]

end Frame

/-! ### The action of `PΩ` on points -/

/-- `Ω` acts on points through its action on vectors. -/
theorem omega_smul_mk (g : StatedOmega ⇑Q) {u : ι → K} (hu : u ≠ 0) :
    g • Projectivization.mk K u hu =
      Projectivization.mk K ((g : GL ι K) • u)
        (fun h => hu (by simpa using congrArg ((g : GL ι K)⁻¹ • ·) h)) := by
  rw [Subgroup.smul_def, Projectivization.smul_mk]

variable (Q) in
/-- The action of `PΩ` on points. -/
noncomputable def omegaHom :
    StatedProj (StatedOmega ⇑Q) →* Equiv.Perm (ℙ K (ι → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom (StatedOmega ⇑Q) (ℙ K (ι → K))) (by
    intro g hg
    rw [MonoidHom.mem_ker]
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
    ext x
    induction x using Projectivization.ind with
    | h u hu =>
    change g • Projectivization.mk K u hu = Projectivization.mk K u hu
    rw [omega_smul_mk, Projectivization.mk_eq_mk_iff]
    refine ⟨c, ?_⟩
    change _ = ((g : GL ι K) : Matrix ι ι K) *ᵥ u
    rw [← hc]
    simp [Matrix.GeneralLinearGroup.scalar, Units.smul_def])

noncomputable instance : MulAction (StatedProj (StatedOmega ⇑Q)) (ℙ K (ι → K)) :=
  MulAction.compHom _ (omegaHom Q)

theorem pomega_smul (g : StatedOmega ⇑Q) (x : ℙ K (ι → K)) :
    (g : StatedProj (StatedOmega ⇑Q)) • x = g • x := rfl

theorem pomega_smul_mk {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) {u : ι → K} (hu : u ≠ 0) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) • Projectivization.mk K u hu =
      Projectivization.mk K (g • u)
        (fun h => hu (by simpa using congrArg (g⁻¹ • ·) h)) := by
  rw [pomega_smul, omega_smul_mk]

theorem singular_mk_iff {u : ι → K} (hu : u ≠ 0) :
    Q (Projectivization.mk K u hu).rep = 0 ↔ Q u = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
  rw [← ha, Units.smul_def, map_smul_eq]
  simp [a.ne_zero]

variable (Q) in
/-- The singular points. -/
def singularPoints : SubMulAction (StatedProj (StatedOmega ⇑Q)) (ℙ K (ι → K)) where
  carrier := {x | Q x.rep = 0}
  smul_mem' g x hx := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    induction x using Projectivization.ind with
    | h u hu =>
    change Q (Projectivization.mk K u hu).rep = 0 at hx
    change Q ((QuotientGroup.mk g : StatedProj (StatedOmega ⇑Q)) •
      Projectivization.mk K u hu).rep = 0
    rw [singular_mk_iff] at hx
    rw [pomega_smul, omega_smul_mk, singular_mk_iff, map_smul_of_mem_omega g.2, hx]

theorem mk_mem_singularPoints {v : ι → K} (hv : v ≠ 0) (hQ : Q v = 0) :
    Projectivization.mk K v hv ∈ singularPoints Q :=
  (singular_mk_iff hv).2 hQ

/-- Perpendicularity of points. -/
def perp (x y : ℙ K (ι → K)) : Prop := polar Q x.rep y.rep = 0

theorem perp_mk {u w : ι → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    perp (Q := Q) (Projectivization.mk K u hu) (Projectivization.mk K w hw) ↔ polar Q u w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  rw [perp, ← ha, ← hb, Units.smul_def, Units.smul_def, polar_smul_left, polar_smul_right]
  simp [a.ne_zero, b.ne_zero]

theorem perp_pomega_smul (g : StatedProj (StatedOmega ⇑Q)) (x y : ℙ K (ι → K)) :
    perp (Q := Q) (g • x) (g • y) ↔ perp (Q := Q) x y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  induction x using Projectivization.ind with
  | h u hu =>
  induction y using Projectivization.ind with
  | h w hw =>
  rw [pomega_smul, pomega_smul, omega_smul_mk, omega_smul_mk, perp_mk, perp_mk,
    polar_smul_of_isometry (map_smul_of_mem_omega g.2)]

/-- An element of `Ω` moving a pair of orthogonal vectors to a non-orthogonal pair is not a
scalar. -/
theorem mk_ne_one {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) {v w : ι → K} (hvw : polar Q v w = 0)
    (hgvw : polar Q (g • v) w ≠ 0) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rintro ⟨c, hc⟩
  apply hgvw
  have : g • v = (c : K) • v := by
    change ((g : GL ι K) : Matrix ι ι K) *ᵥ v = _
    rw [← show ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K)) = g from hc]
    simp [Matrix.GeneralLinearGroup.scalar, Units.smul_def]
  rw [this, polar_smul_left, hvw, smul_zero]

/-! ### The criterion -/

section Criterion

variable {m : ℕ} (F : Frame Q m)

theorem Frame.e_ne_zero (i : Fin m) : F.e i ≠ 0 := fun h => by
  have := F.ef_self i; rw [h, polar_zero_left] at this; exact zero_ne_one this

theorem Frame.f_ne_zero (i : Fin m) : F.f i ≠ 0 := F.swap.e_ne_zero i

/-- The base point `[e₀]`. -/
noncomputable def Frame.basePt (hm : 1 ≤ m) : singularPoints Q :=
  ⟨Projectivization.mk K (F.e ⟨0, hm⟩) (F.e_ne_zero _),
    mk_mem_singularPoints (F.e_ne_zero _) (F.qe _)⟩

/-- Perpendicularity on singular points. -/
def sperp (x y : singularPoints Q) : Prop := perp (Q := Q) (x : ℙ K (ι → K)) y

theorem coe_smul_singular (g : StatedProj (StatedOmega ⇑Q)) (x : singularPoints Q) :
    ((g • x : singularPoints Q) : ℙ K (ι → K)) = g • (x : ℙ K (ι → K)) := rfl

/-- A singular point as `[v]` with `v` singular. -/
theorem singularPoints_ind {P : singularPoints Q → Prop}
    (h : ∀ (v : ι → K) (hv : v ≠ 0) (hQ : Q v = 0),
      P ⟨Projectivization.mk K v hv, mk_mem_singularPoints hv hQ⟩) (x : singularPoints Q) :
    P x := by
  obtain ⟨x, hx⟩ := x
  induction x using Projectivization.ind with
  | h v hv =>
  have hQ : Q v = 0 := by
    change Q (Projectivization.mk K v hv).rep = 0 at hx; rwa [singular_mk_iff] at hx
  exact h v hv hQ

theorem singular_ext {x y : singularPoints Q} (h : (x : ℙ K (ι → K)) = y) : x = y :=
  Subtype.ext h

end Criterion

end CFSGOutside.HallPaige.Orth
