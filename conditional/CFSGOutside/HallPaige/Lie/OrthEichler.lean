import CFSGOutside.Corpus.HallPaige.LieOrth
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Module

/-!
# Eichler transformations and the group `Ω(Q)`

For a quadratic form `Q` on `K^ι` with polar form `B`, a singular vector `u` and `w ⊥ u`, the
Eichler (Siegel) transformation `E(u, w) : x ↦ x + B(x, u) w - B(x, w) u - Q(w) B(x, u) u` is an
isometry; `E(u, v) E(u, w) = E(u, v + w)` and `g E(u, w) g⁻¹ = E(g u, g w)` for isometries `g`.

The commutator identity `⁅E(u, v'), E(v, x)⁆ = E(u, Q(x) v - x)` (for a hyperbolic pair `(v, v')`
orthogonal to `u` and `x`) shows that Eichler transformations lie in the commutator subgroup
`Ω(Q) = StatedOmega Q` of the isometry group, as soon as there are enough hyperbolic pairs
(`CFSGOutside.HallPaige.Orth.Frame.eichGL_mem`): this works in every characteristic, including `q = 2`.
-/

namespace CFSGOutside.HallPaige.Orth

open Matrix QuadraticMap Corpus.Lie
open scoped commutatorElement

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

/-! ### Elements of `GL` from linear maps -/

/-- The element of `GL` given by a pair of mutually inverse linear maps. -/
noncomputable def glOfLin (f g : (ι → K) →ₗ[K] (ι → K)) (hfg : ∀ x, f (g x) = x)
    (hgf : ∀ x, g (f x) = x) : GL ι K where
  val := LinearMap.toMatrix' f
  inv := LinearMap.toMatrix' g
  val_inv := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hfg
  inv_val := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hgf

theorem glOfLin_smul (f g : (ι → K) →ₗ[K] (ι → K)) (hfg hgf) (x : ι → K) :
    glOfLin f g hfg hgf • x = f x :=
  LinearMap.toMatrix'_mulVec f x

theorem gl_smul_def (g : GL ι K) (x : ι → K) : g • x = (g : Matrix ι ι K) *ᵥ x := rfl

theorem gl_ext {g h : GL ι K} (H : ∀ x : ι → K, g • x = h • x) : g = h := by
  apply Units.ext
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun x => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact H x

theorem gl_smul_add (g : GL ι K) (x y : ι → K) : g • (x + y) = g • x + g • y := by
  simp only [gl_smul_def, mulVec_add]

theorem gl_smul_sub (g : GL ι K) (x y : ι → K) : g • (x - y) = g • x - g • y := by
  simp only [gl_smul_def, mulVec_sub]

theorem gl_smul_smul (g : GL ι K) (c : K) (x : ι → K) : g • (c • x) = c • (g • x) := by
  simp only [gl_smul_def, mulVec_smul]

/-! ### The isometry group and `Ω` -/

variable (Q : QuadraticForm K (ι → K))

/-- The isometry group of `Q` (the corpus `isometryCore`). -/
def isoGroup : Subgroup (GL ι K) :=
  Subgroup.closure {A : GL ι K | ∀ v : ι → K, Q (Matrix.mulVec (A : Matrix ι ι K) v) = Q v}

theorem statedOmega_eq : StatedOmega ⇑Q = ⁅isoGroup Q, isoGroup Q⁆ := rfl

variable {Q}

theorem mem_isoGroup {g : GL ι K} (hg : ∀ v : ι → K, Q (g • v) = Q v) : g ∈ isoGroup Q :=
  Subgroup.subset_closure hg

theorem map_smul_of_mem_isoGroup {g : GL ι K} (hg : g ∈ isoGroup Q) (v : ι → K) :
    Q (g • v) = Q v := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem A hA => exact hA v
  | one => simp
  | mul A C _ _ hA hC => rw [mul_smul, hA, hC]
  | inv A _ hA => rw [← hA (A⁻¹ • v), smul_inv_smul]

theorem statedOmega_le_isoGroup : StatedOmega ⇑Q ≤ isoGroup Q := by
  rw [statedOmega_eq, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem map_smul_of_mem_omega {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) (v : ι → K) :
    Q (g • v) = Q v :=
  map_smul_of_mem_isoGroup (statedOmega_le_isoGroup hg) v

theorem polar_smul_of_isometry {g : GL ι K} (hg : ∀ v, Q (g • v) = Q v) (x y : ι → K) :
    polar Q (g • x) (g • y) = polar Q x y := by
  rw [polar, polar, ← gl_smul_add, hg, hg, hg]

theorem commutator_mem_omega {a b : GL ι K} (ha : ∀ v, Q (a • v) = Q v)
    (hb : ∀ v, Q (b • v) = Q v) : ⁅a, b⁆ ∈ StatedOmega ⇑Q :=
  Subgroup.commutator_mem_commutator (mem_isoGroup ha) (mem_isoGroup hb)

/-! ### Polar form bookkeeping -/

theorem map_add_eq (x y : ι → K) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [polar]; ring

theorem polar_self_eq (x : ι → K) : polar Q x x = 2 * Q x := by
  rw [polar_self, two_nsmul, two_mul]

theorem polar_self_of_singular {x : ι → K} (hx : Q x = 0) : polar Q x x = 0 := by
  rw [polar_self_eq, hx, mul_zero]

/-! ### Eichler transformations -/

variable (Q) in
/-- The Eichler transformation `x ↦ x + B(x, u) w - B(x, w) u - Q(w) B(x, u) u`. -/
noncomputable def eichLin (u w : ι → K) : (ι → K) →ₗ[K] (ι → K) where
  toFun x := x + polar Q x u • w - polar Q x w • u - (Q w * polar Q x u) • u
  map_add' x y := by
    simp only [polar_add_left]
    module
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply]
    module

theorem eichLin_apply (u w x : ι → K) :
    eichLin Q u w x = x + polar Q x u • w - polar Q x w • u - (Q w * polar Q x u) • u := rfl

theorem eichLin_eichLin {u v w : ι → K} (hu : Q u = 0) (hv : polar Q u v = 0)
    (hw : polar Q u w = 0) (x : ι → K) :
    eichLin Q u v (eichLin Q u w x) = eichLin Q u (v + w) x := by
  have hvu : polar Q v u = 0 := by rw [polar_comm]; exact hv
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact hw
  have huu : polar Q u u = 0 := polar_self_of_singular hu
  simp only [eichLin_apply, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul,
    polar_add_right, hvu, hwu, huu, hv, hw, map_add_eq v w, polar_comm _ w v]
  module

theorem eichLin_zero (u x : ι → K) : eichLin Q u 0 x = x := by
  simp [eichLin_apply]

theorem eichLin_isometry {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0) (x : ι → K) :
    Q (eichLin Q u w x) = Q x := by
  have hwu : polar Q w u = 0 := by rw [polar_comm]; exact hw
  have huu : polar Q u u = 0 := polar_self_of_singular hu
  have e : eichLin Q u w x =
      x + (polar Q x u • w + (-(polar Q x w + Q w * polar Q x u)) • u) := by
    rw [eichLin_apply]; module
  rw [e, map_add_eq, map_add_eq, QuadraticMap.map_smul, QuadraticMap.map_smul, hu,
    polar_add_right, polar_smul_right, polar_smul_right, polar_smul_left, polar_smul_right,
    hwu]
  simp only [smul_eq_mul]
  rw [polar_comm _ x u]
  ring

variable (Q) in
open Classical in
/-- The Eichler transformation as an element of `GL` (the identity when `u` is not singular or
`w` is not orthogonal to `u`). -/
noncomputable def eichGL (u w : ι → K) : GL ι K :=
  if h : Q u = 0 ∧ polar Q u w = 0 then
    glOfLin (eichLin Q u w) (eichLin Q u (-w))
      (fun x => by
        rw [eichLin_eichLin h.1 h.2 (by rw [polar_neg_right, h.2, neg_zero]), add_neg_cancel,
          eichLin_zero])
      (fun x => by
        rw [eichLin_eichLin h.1 (by rw [polar_neg_right, h.2, neg_zero]) h.2, neg_add_cancel,
          eichLin_zero])
  else 1

variable (Q) in
theorem eichGL_smul {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0) (x : ι → K) :
    eichGL Q u w • x = eichLin Q u w x := by
  rw [eichGL, dif_pos ⟨hu, hw⟩, glOfLin_smul]

theorem eichGL_smul_eq {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0) (x : ι → K) :
    eichGL Q u w • x = x + polar Q x u • w - polar Q x w • u - (Q w * polar Q x u) • u := by
  rw [eichGL_smul Q hu hw, eichLin_apply]

theorem eichGL_isometry {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0) (x : ι → K) :
    Q (eichGL Q u w • x) = Q x := by
  rw [eichGL_smul Q hu hw, eichLin_isometry hu hw]

theorem eichGL_mul {u v w : ι → K} (hu : Q u = 0) (hv : polar Q u v = 0)
    (hw : polar Q u w = 0) : eichGL Q u v * eichGL Q u w = eichGL Q u (v + w) := by
  have hvw : polar Q u (v + w) = 0 := by rw [polar_add_right, hv, hw, add_zero]
  refine gl_ext fun x => ?_
  rw [mul_smul, eichGL_smul Q hu hv, eichGL_smul Q hu hw, eichGL_smul Q hu hvw,
    eichLin_eichLin hu hv hw]

theorem eichGL_zero (u : ι → K) : eichGL Q u 0 = 1 := by
  by_cases hu : Q u = 0
  · refine gl_ext fun x => ?_
    rw [eichGL_smul Q hu (by rw [polar_zero_right]), eichLin_zero, one_smul]
  · rw [eichGL, dif_neg (fun h => hu h.1)]

theorem eichGL_inv {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0) :
    (eichGL Q u w)⁻¹ = eichGL Q u (-w) := by
  rw [inv_eq_iff_mul_eq_one, eichGL_mul hu hw (by rw [polar_neg_right, hw, neg_zero]),
    add_neg_cancel, eichGL_zero]

theorem eichGL_smul_self {u : ι → K} (hu : Q u = 0) (c : K) : eichGL Q u (c • u) = 1 := by
  have huu : polar Q u u = 0 := polar_self_of_singular hu
  refine gl_ext fun x => ?_
  rw [eichGL_smul_eq hu (by rw [polar_smul_right, huu, smul_zero]), one_smul,
    QuadraticMap.map_smul, hu, polar_smul_right]
  simp only [smul_eq_mul, mul_zero, zero_mul, zero_smul, sub_zero]
  module

/-- Conjugating an Eichler transformation by an isometry. -/
theorem conj_eichGL {g : GL ι K} (hg : ∀ v, Q (g • v) = Q v) {u w : ι → K} (hu : Q u = 0)
    (hw : polar Q u w = 0) : g * eichGL Q u w * g⁻¹ = eichGL Q (g • u) (g • w) := by
  have hu' : Q (g • u) = 0 := by rw [hg, hu]
  have hw' : polar Q (g • u) (g • w) = 0 := by rw [polar_smul_of_isometry hg, hw]
  refine gl_ext fun x => ?_
  have hx : ∀ y, polar Q (g⁻¹ • x) y = polar Q x (g • y) := fun y => by
    rw [← polar_smul_of_isometry hg, smul_inv_smul]
  rw [mul_smul, mul_smul, eichGL_smul_eq hu hw, eichGL_smul_eq hu' hw', hx, hx, hg,
    gl_smul_sub, gl_smul_sub, gl_smul_add, gl_smul_smul, gl_smul_smul, gl_smul_smul,
    smul_inv_smul]

/-- **The commutator identity.** For a hyperbolic pair `(v, v')` orthogonal to the singular
vector `u` and to `x`, `⁅E(u, v'), E(v, x)⁆ = E(u, Q(x) v - x)`. -/
theorem commutator_eichGL {u v v' x : ι → K} (hu : Q u = 0) (hv : Q v = 0)
    (hvv' : polar Q v v' = 1) (huv : polar Q u v = 0) (huv' : polar Q u v' = 0)
    (hux : polar Q u x = 0) (hvx : polar Q v x = 0) (hv'x : polar Q v' x = 0) :
    ⁅eichGL Q u v', eichGL Q v x⁆ = eichGL Q u (Q x • v - x) := by
  have hb : ∀ y, Q (eichGL Q v x • y) = Q y := eichGL_isometry hv hvx
  have hvu : polar Q v u = 0 := by rw [polar_comm]; exact huv
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hux
  have hbu : eichGL Q v x • u = u := by
    rw [eichGL_smul_eq hv hvx, huv, hux]; simp
  have hbv' : eichGL Q v x • (-v') = -(v' + x - Q x • v) := by
    rw [eichGL_smul_eq hv hvx, polar_neg_left, polar_neg_left, polar_comm _ v' v, hvv', hv'x]
    module
  have hneg : polar Q u (-v') = 0 := by rw [polar_neg_right, huv', neg_zero]
  have h2 : polar Q u (-(v' + x - Q x • v)) = 0 := by
    rw [polar_neg_right, polar_sub_right, polar_add_right, polar_smul_right, huv', hux, huv]
    simp
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (eichGL Q v x),
    eichGL_inv hu huv', conj_eichGL hb hu hneg, hbu, hbv', eichGL_mul hu huv' h2]
  congr 1
  module

/-- An Eichler transformation is in `Ω` as soon as two suitable hyperbolic pairs exist:
`(v, v')` orthogonal to `u` and `w`, and `(t, t')` orthogonal to `u` and `v`. -/
theorem eichGL_mem_omega_of_pairs {u v v' t t' w : ι → K} (hu : Q u = 0) (hv : Q v = 0)
    (hvv' : polar Q v v' = 1) (ht : Q t = 0) (htt' : polar Q t t' = 1)
    (huv : polar Q u v = 0) (huv' : polar Q u v' = 0) (hut : polar Q u t = 0)
    (hut' : polar Q u t' = 0) (hvt : polar Q v t = 0) (hvt' : polar Q v t' = 0)
    (huw : polar Q u w = 0) (hvw : polar Q v w = 0) (hv'w : polar Q v' w = 0) :
    eichGL Q u w ∈ StatedOmega ⇑Q := by
  -- `E(u, c v) ∈ Ω` from the pair `(t, t')`
  have hcv : ∀ c : K, eichGL Q u (c • v) ∈ StatedOmega ⇑Q := by
    intro c
    have h := commutator_eichGL (x := -(c • v)) hu ht htt' hut hut'
      (by rw [polar_neg_right, polar_smul_right, huv, smul_zero, neg_zero])
      (by rw [polar_neg_right, polar_smul_right, polar_comm, hvt, smul_zero, neg_zero])
      (by rw [polar_neg_right, polar_smul_right, polar_comm, hvt', smul_zero, neg_zero])
    rw [QuadraticMap.map_neg, QuadraticMap.map_smul, hv, smul_zero, zero_smul, zero_sub,
      neg_neg] at h
    rw [← h]
    exact commutator_mem_omega (eichGL_isometry hu hut') (eichGL_isometry ht
      (by rw [polar_neg_right, polar_smul_right, polar_comm, hvt, smul_zero, neg_zero]))
  have h1 := commutator_eichGL (x := -w) hu hv hvv' huv huv'
    (by rw [polar_neg_right, huw, neg_zero]) (by rw [polar_neg_right, hvw, neg_zero])
    (by rw [polar_neg_right, hv'w, neg_zero])
  have hm1 : eichGL Q u (Q w • v + w) ∈ StatedOmega ⇑Q := by
    rw [QuadraticMap.map_neg, sub_neg_eq_add] at h1
    rw [← h1]
    exact commutator_mem_omega (eichGL_isometry hu huv') (eichGL_isometry hv
      (by rw [polar_neg_right, hvw, neg_zero]))
  have hp : eichGL Q u (Q w • v + w) * eichGL Q u ((-Q w) • v) = eichGL Q u w := by
    rw [eichGL_mul hu (by rw [polar_add_right, polar_smul_right, huv, huw]; simp)
      (by rw [polar_smul_right, huv, smul_zero])]
    congr 1
    module
  rw [← hp]
  exact mul_mem hm1 (hcv _)

/-! ### Hyperbolic frames -/

variable (Q) in
/-- A family of `m` mutually orthogonal hyperbolic pairs `(e i, f i)`. -/
structure Frame (m : ℕ) where
  /-- The first vectors of the pairs. -/
  e : Fin m → ι → K
  /-- The second vectors of the pairs. -/
  f : Fin m → ι → K
  qe : ∀ i, Q (e i) = 0
  qf : ∀ i, Q (f i) = 0
  ee : ∀ i j, polar Q (e i) (e j) = 0
  ff : ∀ i j, polar Q (f i) (f j) = 0
  ef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0

namespace Frame

variable {m : ℕ} (F : Frame Q m)

/-- The frame with the two vectors of each pair exchanged. -/
def swap : Frame Q m where
  e := F.f
  f := F.e
  qe := F.qf
  qf := F.qe
  ee := F.ff
  ff := F.ee
  ef i j := by rw [polar_comm, F.ef j i]; simp only [eq_comm]

theorem fe (i j : Fin m) : polar Q (F.f i) (F.e j) = if i = j then 1 else 0 := F.swap.ef i j

theorem ef_self (i : Fin m) : polar Q (F.e i) (F.f i) = 1 := by rw [F.ef, if_pos rfl]

theorem fe_self (i : Fin m) : polar Q (F.f i) (F.e i) = 1 := by rw [F.fe, if_pos rfl]

theorem ef_ne {i j : Fin m} (h : i ≠ j) : polar Q (F.e i) (F.f j) = 0 := by rw [F.ef, if_neg h]

theorem fe_ne {i j : Fin m} (h : i ≠ j) : polar Q (F.f i) (F.e j) = 0 := by rw [F.fe, if_neg h]

/-- The component of `w` in the `j`-th hyperbolic plane. -/
def comp (j : Fin m) (w : ι → K) : ι → K := polar Q w (F.f j) • F.e j + polar Q w (F.e j) • F.f j

theorem polar_comp_e (j k : Fin m) (w : ι → K) :
    polar Q (F.comp j w) (F.e k) = if j = k then polar Q w (F.e k) else 0 := by
  rw [comp, polar_add_left, polar_smul_left, polar_smul_left, F.ee, F.fe]
  split_ifs with h
  · subst h; simp
  · simp

theorem polar_comp_f (j k : Fin m) (w : ι → K) :
    polar Q (F.comp j w) (F.f k) = if j = k then polar Q w (F.f k) else 0 := by
  rw [comp, polar_add_left, polar_smul_left, polar_smul_left, F.ef, F.ff]
  split_ifs with h
  · subst h; simp
  · simp

/-- The part of `w` orthogonal to the planes indexed by `S`. -/
def rest (S : Finset (Fin m)) (w : ι → K) : ι → K := w - ∑ j ∈ S, F.comp j w

theorem polar_sum_left (S : Finset (Fin m)) (g : Fin m → ι → K) (y : ι → K) :
    polar Q (∑ j ∈ S, g j) y = ∑ j ∈ S, polar Q (g j) y := by
  induction S using Finset.induction_on with
  | empty => simp [polar_zero_left]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_left, ih]

theorem polar_rest_e (S : Finset (Fin m)) (w : ι → K) {k : Fin m} (hk : k ∈ S) :
    polar Q (F.rest S w) (F.e k) = 0 := by
  rw [rest, polar_sub_left, polar_sum_left]
  simp only [polar_comp_e, Finset.sum_ite_eq', if_pos hk, sub_self]

theorem polar_rest_f (S : Finset (Fin m)) (w : ι → K) {k : Fin m} (hk : k ∈ S) :
    polar Q (F.rest S w) (F.f k) = 0 := by
  rw [rest, polar_sub_left, polar_sum_left]
  simp only [polar_comp_f, Finset.sum_ite_eq', if_pos hk, sub_self]

/-- If `y` is orthogonal to the planes indexed by `S`, then `B(y, rest w) = B(y, w)`. -/
theorem polar_rest_right (S : Finset (Fin m)) (w : ι → K) {y : ι → K}
    (hy : ∀ k ∈ S, polar Q y (F.e k) = 0 ∧ polar Q y (F.f k) = 0) :
    polar Q y (F.rest S w) = polar Q y w := by
  rw [rest, polar_sub_right, polar_comm _ y (∑ j ∈ S, F.comp j w), polar_sum_left]
  rw [Finset.sum_eq_zero, sub_zero]
  intro j hj
  rw [comp, polar_add_left, polar_smul_left, polar_smul_left, polar_comm _ (F.e j),
    polar_comm _ (F.f j), (hy j hj).1, (hy j hj).2]
  simp

theorem exists_ne_ne (hm : 3 ≤ m) (i j : Fin m) : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
  by_contra h
  push Not at h
  have : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := fun k _ => by
    by_cases hk : k = i
    · simp [hk]
    · simp [h k hk]
  have := Finset.card_le_card this
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_two (a := i) (b := j)
  omega

/-- **Eichler transformations at a frame vector lie in `Ω`.** -/
theorem eichGL_mem (hm : 3 ≤ m) (i : Fin m) {w : ι → K} (hw : polar Q (F.e i) w = 0) :
    eichGL Q (F.e i) w ∈ StatedOmega ⇑Q := by
  set u := F.e i
  have hu : Q u = 0 := F.qe i
  let A : AddSubgroup (ι → K) :=
    { carrier := {w | polar Q u w = 0 ∧ eichGL Q u w ∈ StatedOmega ⇑Q}
      add_mem' := fun {a b} ha hb => ⟨by rw [polar_add_right, ha.1, hb.1, add_zero], by
        rw [← eichGL_mul hu ha.1 hb.1]; exact mul_mem ha.2 hb.2⟩
      zero_mem' := ⟨polar_zero_right _ _, by rw [eichGL_zero]; exact one_mem _⟩
      neg_mem' := fun {a} ha => ⟨by rw [polar_neg_right, ha.1, neg_zero], by
        rw [← eichGL_inv hu ha.1]; exact inv_mem ha.2⟩ }
  -- the pieces in the other planes
  have hcomp : ∀ j, j ≠ i → F.comp j w ∈ A := by
    intro j hji
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne hm i j
    have hperp : ∀ l, l ≠ j → polar Q (F.e l) (F.comp j w) = 0 ∧
        polar Q (F.f l) (F.comp j w) = 0 := fun l hl => by
      rw [polar_comm, polar_comm _ (F.f l), polar_comp_e, polar_comp_f, if_neg (Ne.symm hl),
        if_neg (Ne.symm hl)]
      exact ⟨rfl, rfl⟩
    refine ⟨(hperp i (Ne.symm hji)).1, ?_⟩
    exact eichGL_mem_omega_of_pairs hu (F.qe k) (F.ef_self k) (F.qe j) (F.ef_self j)
      (F.ee i k) (F.ef_ne (Ne.symm hki)) (F.ee i j) (F.ef_ne (Ne.symm hji)) (F.ee k j)
      (F.ef_ne hkj) (hperp i (Ne.symm hji)).1 (hperp k hkj).1 (hperp k hkj).2
  have hrest : F.rest Finset.univ w ∈ A := by
    obtain ⟨k, hki, -⟩ := exists_ne_ne hm i i
    obtain ⟨l, hli, hlk⟩ := exists_ne_ne hm i k
    have hperp : ∀ l, polar Q (F.e l) (F.rest Finset.univ w) = 0 ∧
        polar Q (F.f l) (F.rest Finset.univ w) = 0 := fun l => by
      rw [polar_comm, polar_comm _ (F.f l)]
      exact ⟨F.polar_rest_e _ _ (Finset.mem_univ _), F.polar_rest_f _ _ (Finset.mem_univ _)⟩
    refine ⟨(hperp i).1, ?_⟩
    exact eichGL_mem_omega_of_pairs hu (F.qe k) (F.ef_self k) (F.qe l) (F.ef_self l)
      (F.ee i k) (F.ef_ne (Ne.symm hki)) (F.ee i l) (F.ef_ne (Ne.symm hli)) (F.ee k l)
      (F.ef_ne (Ne.symm hlk)) (hperp i).1 (hperp k).1 (hperp k).2
  have hself : F.comp i w ∈ A := by
    have : F.comp i w = polar Q w (F.f i) • u := by
      rw [comp, polar_comm _ w (F.e i), hw, zero_smul, add_zero]
    rw [this]
    refine ⟨by rw [polar_smul_right, polar_self_of_singular hu, smul_zero], ?_⟩
    rw [eichGL_smul_self hu]
    exact one_mem _
  have hw' : w = F.rest Finset.univ w + ∑ j, F.comp j w := by
    rw [rest, sub_add_cancel]
  have : w ∈ A := by
    rw [hw']
    refine add_mem hrest (sum_mem fun j _ => ?_)
    by_cases hj : j = i
    · subst hj; exact hself
    · exact hcomp j hj
  exact this.2

/-- The same for the second vectors of the pairs. -/
theorem eichGL_mem_f (hm : 3 ≤ m) (i : Fin m) {w : ι → K} (hw : polar Q (F.f i) w = 0) :
    eichGL Q (F.f i) w ∈ StatedOmega ⇑Q :=
  F.swap.eichGL_mem hm i hw

end Frame

end CFSGOutside.HallPaige.Orth
