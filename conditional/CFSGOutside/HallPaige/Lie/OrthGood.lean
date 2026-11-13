import CFSGOutside.HallPaige.Lie.OrthCriterion

/-!
# Goodness of the point stabilizer in `PΩ(Q)`

The stabilizer of the singular point `[e₀]` contains two distinct commuting involutions:

* characteristic `2`: the Eichler transformations `E(e₀, e₁)` and `E(e₀, f₁)`;
* otherwise: `s₁, s₂`, where `s_j` is the square of the Weyl element
  `E(e₀, e_j) E(f_j, -f₀) E(e₀, e_j)`; it is `-1` on the hyperbolic planes `0` and `j` and the
  identity on their orthogonal complement.

Hence `CFSGOutside.HallPaige.Orth.wilcoxCriterion_omega`: `PΩ(Q)` satisfies the Wilcox criterion.
-/

namespace CFSGOutside.HallPaige.Orth

open Matrix QuadraticMap Corpus.Lie MulAction
open scoped LinearAlgebra.Projectivization

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

namespace Frame

variable {m : ℕ} (F : Frame Q m)

theorem mem_stabilizer_basePt (hm : 1 ≤ m) {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) {c : K}
    (hc : c ≠ 0) (h : g • F.e ⟨0, hm⟩ = c • F.e ⟨0, hm⟩) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) ∈
      stabilizer (StatedProj (StatedOmega ⇑Q)) (F.basePt hm) := by
  rw [mem_stabilizer_iff]
  apply singular_ext
  rw [coe_smul_singular]
  change _ • Projectivization.mk K _ _ = Projectivization.mk K _ _
  rw [pomega_smul_mk]
  exact mk_eq_mk_of_eq_smul _ _ hc h

theorem mk_sq_eq_one {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) (h : g * g = 1) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) ^ 2 = 1 := by
  rw [_root_.sq, ← QuotientGroup.mk_mul, show (⟨g, hg⟩ * ⟨g, hg⟩ : StatedOmega ⇑Q) = 1 from
    Subtype.ext h, QuotientGroup.mk_one]

theorem mk_comm {g h : GL ι K} (hg : g ∈ StatedOmega ⇑Q) (hh : h ∈ StatedOmega ⇑Q)
    (hgh : g * h = h * g) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) * (⟨h, hh⟩ : StatedOmega ⇑Q) =
      (⟨h, hh⟩ : StatedOmega ⇑Q) * (⟨g, hg⟩ : StatedOmega ⇑Q) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    show (⟨g, hg⟩ * ⟨h, hh⟩ : StatedOmega ⇑Q) = ⟨h, hh⟩ * ⟨g, hg⟩ from Subtype.ext hgh]

theorem mk_ne_mk {g h : GL ι K} (hg : g ∈ StatedOmega ⇑Q) (hh : h ∈ StatedOmega ⇑Q)
    {v w : ι → K} (hvw : polar Q v w = 0) (hgvw : polar Q ((g⁻¹ * h) • v) w ≠ 0) :
    ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) ≠ (⟨h, hh⟩ : StatedOmega ⇑Q) := by
  intro H
  apply mk_ne_one (mul_mem (inv_mem hg) hh) hvw hgvw
  rw [show (⟨g⁻¹ * h, mul_mem (inv_mem hg) hh⟩ : StatedOmega ⇑Q) =
      (⟨g, hg⟩ : StatedOmega ⇑Q)⁻¹ * ⟨h, hh⟩ from rfl, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    H, inv_mul_cancel]

/-! ### Characteristic `2` -/

theorem polar_eichGL_e_smul {i : Fin m} {w v : ι → K} (hw : polar Q (F.e i) w = 0)
    (hv : polar Q v (F.e i) = 0) (y : ι → K) :
    polar Q (eichGL Q (F.e i) w • v) y = polar Q v y - polar Q v w * polar Q (F.e i) y := by
  rw [eichGL_smul_eq (F.qe i) hw, hv, polar_sub_left, polar_sub_left, polar_add_left,
    polar_smul_left, polar_smul_left, polar_smul_left]
  simp

/-- In characteristic `2` the point stabilizer is good. -/
theorem isGood_stabilizer_of_two_eq_zero [Finite K] (hm : 3 ≤ m) (h2 : (2 : K) = 0) :
    IsGood (stabilizer (StatedProj (StatedOmega ⇑Q)) (F.basePt (by omega))) := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hw1 : polar Q (F.e i0) (F.e i1) = 0 := F.ee _ _
  have hw2 : polar Q (F.e i0) (F.f i1) = 0 := F.ef_ne h01
  have ha := F.eichGL_mem hm i0 hw1
  have hb := F.eichGL_mem hm i0 hw2
  have hsq : ∀ {w : ι → K}, polar Q (F.e i0) w = 0 →
      eichGL Q (F.e i0) w * eichGL Q (F.e i0) w = 1 := fun {w} hw => by
    rw [eichGL_mul (F.qe i0) hw hw, ← two_smul K w, h2, zero_smul, eichGL_zero]
  refine Subgroup.isGood_of_commuting_involutions _
    (F.mem_stabilizer_basePt (by omega) ha one_ne_zero
      (by rw [one_smul]; exact eichGL_smul_self_vec (F.qe i0) hw1))
    (F.mem_stabilizer_basePt (by omega) hb one_ne_zero
      (by rw [one_smul]; exact eichGL_smul_self_vec (F.qe i0) hw2))
    (mk_sq_eq_one ha (hsq hw1)) (mk_sq_eq_one hb (hsq hw2))
    (mk_comm ha hb (by rw [eichGL_mul (F.qe i0) hw1 hw2, eichGL_mul (F.qe i0) hw2 hw1, add_comm]))
    ?_ ?_ ?_
  · refine mk_ne_one ha (v := F.f i1) (w := F.f i0) (F.ff _ _) ?_
    rw [F.polar_eichGL_e_smul hw1 (F.fe_ne (Ne.symm h01)), F.ff, F.fe_self, F.ef_self]
    norm_num
  · refine mk_ne_one hb (v := F.e i1) (w := F.f i0) (F.ef_ne (Ne.symm h01)) ?_
    rw [F.polar_eichGL_e_smul hw2 (F.ee _ _), F.ef_ne (Ne.symm h01), F.ef_self, F.ef_self]
    norm_num
  · refine mk_ne_mk ha hb (v := F.e i1) (w := F.f i0) (F.ef_ne (Ne.symm h01)) ?_
    have hw3 : polar Q (F.e i0) (-F.e i1) = 0 := by rw [polar_neg_right, hw1, neg_zero]
    rw [eichGL_inv (F.qe i0) hw1, eichGL_mul (F.qe i0) hw3 hw2,
      F.polar_eichGL_e_smul (by rw [polar_add_right, hw3, hw2, add_zero]) (F.ee _ _),
      F.ef_ne (Ne.symm h01), polar_add_right, polar_neg_right, F.ee, F.ef_self, F.ef_self]
    norm_num

/-! ### Odd characteristic -/

/-- The Weyl element `E(e i, e j) E(f j, -f i) E(e i, e j)`. -/
noncomputable def weylGL (i j : Fin m) : GL ι K :=
  eichGL Q (F.e i) (F.e j) * eichGL Q (F.f j) (-F.f i) * eichGL Q (F.e i) (F.e j)

theorem weylGL_mem (hm : 3 ≤ m) (i j : Fin m) : F.weylGL i j ∈ StatedOmega ⇑Q :=
  mul_mem (mul_mem (F.eichGL_mem hm i (F.ee i j))
    (F.eichGL_mem_f hm j (by rw [polar_neg_right, F.ff, neg_zero])))
    (F.eichGL_mem hm i (F.ee i j))

theorem weylGL_smul {i j : Fin m} (hij : i ≠ j) (v : ι → K) :
    F.weylGL i j • v = v - F.comp i v - F.comp j v + polar Q v (F.f i) • F.f j +
      polar Q v (F.e i) • F.e j - polar Q v (F.f j) • F.f i - polar Q v (F.e j) • F.e i := by
  have h1 : polar Q (F.e i) (F.e j) = 0 := F.ee i j
  have h2 : polar Q (F.f j) (-F.f i) = 0 := by rw [polar_neg_right, F.ff, neg_zero]
  rw [weylGL, mul_smul, mul_smul, eichGL_smul_eq (F.qe i) h1, eichGL_smul_eq (F.qf j) h2,
    eichGL_smul_eq (F.qe i) h1]
  simp only [comp, polar_add_left, polar_sub_left, polar_smul_left, polar_neg_right,
    polar_neg_left, QuadraticMap.map_neg, F.qe, F.qf, F.ee, F.ff, F.ef_self, F.fe_self, F.ef_ne hij,
    F.ef_ne (Ne.symm hij), F.fe_ne hij, F.fe_ne (Ne.symm hij), smul_eq_mul]
  module

/-- The square of the Weyl element: `-1` on the planes `i` and `j`. -/
noncomputable def signGL (i j : Fin m) : GL ι K := F.weylGL i j * F.weylGL i j

theorem signGL_smul {i j : Fin m} (hij : i ≠ j) (v : ι → K) :
    F.signGL i j • v = v - (2 : K) • F.comp i v - (2 : K) • F.comp j v := by
  rw [signGL, mul_smul, F.weylGL_smul hij, F.weylGL_smul hij]
  simp only [comp, polar_add_left, polar_sub_left, polar_smul_left, F.ee, F.ff, F.ef_self,
    F.fe_self, F.ef_ne hij, F.ef_ne (Ne.symm hij), F.fe_ne hij, F.fe_ne (Ne.symm hij),
    smul_eq_mul]
  module

theorem polar_signGL_smul {i j : Fin m} (hij : i ≠ j) (v y : ι → K) :
    polar Q (F.signGL i j • v) y = polar Q v y - 2 * (polar Q v (F.f i) * polar Q (F.e i) y +
      polar Q v (F.e i) * polar Q (F.f i) y + polar Q v (F.f j) * polar Q (F.e j) y +
      polar Q v (F.e j) * polar Q (F.f j) y) := by
  rw [F.signGL_smul hij]
  simp only [comp, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul]
  ring

theorem signGL_mem (hm : 3 ≤ m) (i j : Fin m) : F.signGL i j ∈ StatedOmega ⇑Q :=
  mul_mem (F.weylGL_mem hm i j) (F.weylGL_mem hm i j)

theorem signGL_mul_self {i j : Fin m} (hij : i ≠ j) : F.signGL i j * F.signGL i j = 1 := by
  refine gl_ext fun v => ?_
  rw [mul_smul, F.signGL_smul hij, F.signGL_smul hij, one_smul]
  simp only [comp, polar_add_left, polar_sub_left, polar_smul_left, F.ee, F.ff, F.ef_self,
    F.fe_self, F.ef_ne hij, F.ef_ne (Ne.symm hij), F.fe_ne hij, F.fe_ne (Ne.symm hij),
    smul_eq_mul]
  module

theorem signGL_comm {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    F.signGL i j * F.signGL i k = F.signGL i k * F.signGL i j := by
  refine gl_ext fun v => ?_
  rw [mul_smul, mul_smul, F.signGL_smul hij, F.signGL_smul hik, F.signGL_smul hij,
    F.signGL_smul hik]
  simp only [comp, polar_add_left, polar_sub_left, polar_smul_left, F.ee, F.ff, F.ef_self,
    F.fe_self, F.ef_ne hij, F.ef_ne (Ne.symm hij), F.fe_ne hij, F.fe_ne (Ne.symm hij),
    F.ef_ne hik, F.ef_ne (Ne.symm hik), F.fe_ne hik, F.fe_ne (Ne.symm hik),
    F.ef_ne hjk, F.ef_ne (Ne.symm hjk), F.fe_ne hjk, F.fe_ne (Ne.symm hjk), smul_eq_mul]
  module

/-- Away from characteristic `2` the point stabilizer is good. -/
theorem isGood_stabilizer_of_two_ne_zero [Finite K] (hm : 3 ≤ m) (h2 : (2 : K) ≠ 0) :
    IsGood (stabilizer (StatedProj (StatedOmega ⇑Q)) (F.basePt (by omega))) := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, hm⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have ha := F.signGL_mem hm i0 i1
  have hb := F.signGL_mem hm i0 i2
  have hfix : ∀ {j}, i0 ≠ j → F.signGL i0 j • F.e i0 = (-1 : K) • F.e i0 := fun {j} hj => by
    rw [F.signGL_smul hj]
    simp only [comp, F.ee, F.ef_self, F.ef_ne hj, zero_smul, add_zero, one_smul]
    module
  have hvals : ∀ {j k : Fin m}, j ≠ k → polar Q (F.e j) (F.f k) = 0 ∧
      polar Q (F.f j) (F.e k) = 0 := fun h => ⟨F.ef_ne h, F.fe_ne h⟩
  refine Subgroup.isGood_of_commuting_involutions _
    (F.mem_stabilizer_basePt (by omega) ha (neg_ne_zero.2 one_ne_zero) (hfix h01))
    (F.mem_stabilizer_basePt (by omega) hb (neg_ne_zero.2 one_ne_zero) (hfix h02))
    (mk_sq_eq_one ha (F.signGL_mul_self h01)) (mk_sq_eq_one hb (F.signGL_mul_self h02))
    (mk_comm ha hb (F.signGL_comm h01 h02 h12)) ?_ ?_ ?_
  · refine mk_ne_one ha (v := F.e i1 + F.e i2) (w := F.f i1 - F.f i2) ?_ ?_
    · simp only [polar_add_left, polar_sub_right, F.ef_self, F.ef_ne h12, F.ef_ne (Ne.symm h12)]
      ring
    · rw [F.polar_signGL_smul h01]
      simp only [polar_add_left, polar_sub_right, F.ef_self, F.ee, F.ff, F.fe_self,
        (hvals h01).1, (hvals h01).2, (hvals h02).1, (hvals h02).2, (hvals h12).1, (hvals h12).2,
        (hvals (Ne.symm h01)).1, (hvals (Ne.symm h01)).2, (hvals (Ne.symm h02)).1,
        (hvals (Ne.symm h02)).2, (hvals (Ne.symm h12)).1, (hvals (Ne.symm h12)).2]
      ring_nf
      exact neg_ne_zero.2 h2
  · refine mk_ne_one hb (v := F.e i2 + F.e i1) (w := F.f i2 - F.f i1) ?_ ?_
    · simp only [polar_add_left, polar_sub_right, F.ef_self, F.ef_ne h12, F.ef_ne (Ne.symm h12)]
      ring
    · rw [F.polar_signGL_smul h02]
      simp only [polar_add_left, polar_sub_right, F.ef_self, F.ee, F.ff, F.fe_self,
        (hvals h01).1, (hvals h01).2, (hvals h02).1, (hvals h02).2, (hvals h12).1, (hvals h12).2,
        (hvals (Ne.symm h01)).1, (hvals (Ne.symm h01)).2, (hvals (Ne.symm h02)).1,
        (hvals (Ne.symm h02)).2, (hvals (Ne.symm h12)).1, (hvals (Ne.symm h12)).2]
      ring_nf
      exact neg_ne_zero.2 h2
  · refine mk_ne_mk ha hb (v := F.e i0 + F.e i1) (w := F.f i0 - F.f i1) ?_ ?_
    · simp only [polar_add_left, polar_sub_right, F.ef_self, F.ef_ne h01, F.ef_ne (Ne.symm h01)]
      ring
    · have hinv : (F.signGL i0 i1)⁻¹ = F.signGL i0 i1 :=
        inv_eq_of_mul_eq_one_right (F.signGL_mul_self h01)
      rw [hinv, mul_smul, F.polar_signGL_smul h01]
      simp only [F.polar_signGL_smul h02, polar_add_left, polar_sub_right, F.ef_self, F.ee, F.ff,
        F.fe_self, (hvals h01).1, (hvals h01).2, (hvals h02).1, (hvals h02).2, (hvals h12).1,
        (hvals h12).2, (hvals (Ne.symm h01)).1, (hvals (Ne.symm h01)).2, (hvals (Ne.symm h02)).1,
        (hvals (Ne.symm h02)).2, (hvals (Ne.symm h12)).1, (hvals (Ne.symm h12)).2]
      ring_nf
      exact h2

end Frame

/-- **The Wilcox criterion for `PΩ(Q)`**: a quadratic form with nondegenerate polar form and at
least three mutually orthogonal hyperbolic pairs. -/
theorem wilcoxCriterion_omega [Finite K] {m : ℕ} (F : Frame Q m) (hm : 3 ≤ m)
    (hnd : ∀ y : ι → K, y ≠ 0 → ∃ w, polar Q y w ≠ 0) :
    WilcoxCriterion (StatedProj (StatedOmega ⇑Q)) := by
  refine Frame.wilcoxCriterion_omega_of_isGood F hm hnd ?_
  by_cases h2 : (2 : K) = 0
  · exact F.isGood_stabilizer_of_two_eq_zero hm h2
  · exact F.isGood_stabilizer_of_two_ne_zero hm h2

end CFSGOutside.HallPaige.Orth
