import CFSGOutside.HallPaige.Lie.OrthPolar

/-!
# The polar-space criterion for `PΩ(Q)`

`CFSGOutside.HallPaige.Orth.wilcoxCriterion_omega_of_isGood`: for a quadratic form with nondegenerate polar
form and a frame of at least three hyperbolic pairs, `PΩ(Q)` acting on the singular points
satisfies the hypotheses of `CFSGOutside.HallPaige.wilcoxCriterion_of_polar`, apart from the goodness of the
point stabilizer.
-/

namespace CFSGOutside.HallPaige.Orth

open Matrix QuadraticMap Corpus.Lie MulAction
open scoped LinearAlgebra.Projectivization

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {Q : QuadraticForm K (ι → K)}

theorem mk_eq_mk_of_eq_smul {a b : ι → K} (ha : a ≠ 0) (hb : b ≠ 0) {c : K} (hc : c ≠ 0)
    (h : a = c • b) : Projectivization.mk K a ha = Projectivization.mk K b hb :=
  (Projectivization.mk_eq_mk_iff _ _ _ _ _).2 ⟨Units.mk0 c hc, by rw [h]; rfl⟩

theorem mk_ne_mk_of_polar {a b : ι → K} (ha : a ≠ 0) (hb : b ≠ 0) {w : ι → K}
    (haw : polar Q a w ≠ 0) (hbw : polar Q b w = 0) :
    Projectivization.mk K a ha ≠ Projectivization.mk K b hb := by
  rw [Ne, Projectivization.mk_eq_mk_iff]
  rintro ⟨u, hu⟩
  apply haw
  rw [← hu, Units.smul_def, polar_smul_left, hbw, smul_zero]

theorem eichGL_smul_self_vec {u x : ι → K} (hu : Q u = 0) (hx : polar Q u x = 0) :
    eichGL Q u x • u = u :=
  eichGL_smul_fix hu hx (polar_self_of_singular hu) hx

namespace Frame

variable {m : ℕ} (F : Frame Q m)

theorem Q_hyp {i k : Fin m} (hik : i ≠ k) : Q ((F.e i + F.f i) + (F.e k - F.f k)) = 0 := by
  have hki : k ≠ i := Ne.symm hik
  simp only [map_add_eq, map_sub_eq, polar_add_left, polar_add_right, polar_sub_left,
    polar_sub_right, F.qe, F.qf, F.ef_self, F.ee, F.ff, F.ef_ne hik, F.fe_ne hik,
    F.ef_ne hki, F.fe_ne hki]
  ring

/-- **The polar-space criterion for `PΩ(Q)`.** -/
theorem wilcoxCriterion_omega_of_isGood [Finite K] (hm : 3 ≤ m)
    (hnd : ∀ y : ι → K, y ≠ 0 → ∃ w, polar Q y w ≠ 0)
    (hgood : IsGood (stabilizer (StatedProj (StatedOmega ⇑Q)) (F.basePt (by omega)))) :
    WilcoxCriterion (StatedProj (StatedOmega ⇑Q)) := by
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, hm⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have he0 := F.e_ne_zero i0
  have hx₀ : F.basePt (by omega) = ⟨Projectivization.mk K (F.e i0) he0,
      mk_mem_singularPoints he0 (F.qe i0)⟩ := rfl
  have hpt : ∀ {g : GL ι K} (hg : g ∈ StatedOmega ⇑Q) {u : ι → K} (hu : u ≠ 0) (hQu : Q u = 0)
      {v : ι → K} (hv : v ≠ 0) (hQv : Q v = 0) {c : K} (hc : c ≠ 0) (h : g • u = c • v),
      ((⟨g, hg⟩ : StatedOmega ⇑Q) : StatedProj (StatedOmega ⇑Q)) •
        (⟨Projectivization.mk K u hu, mk_mem_singularPoints hu hQu⟩ : singularPoints Q) =
        ⟨Projectivization.mk K v hv, mk_mem_singularPoints hv hQv⟩ := by
    intro g hg u hu hQu v hv hQv c hc h
    apply singular_ext
    rw [coe_smul_singular, pomega_smul_mk]
    exact mk_eq_mk_of_eq_smul _ _ hc h
  have hsperp : ∀ {u v : ι → K} (hu : u ≠ 0) (hv : v ≠ 0) {p q},
      sperp (Q := Q) ⟨Projectivization.mk K u hu, p⟩ ⟨Projectivization.mk K v hv, q⟩ ↔
        polar Q u v = 0 :=
    fun hu hv => perp_mk hu hv
  refine wilcoxCriterion_of_polar (sperp (Q := Q)) (F.basePt (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hgood
  · -- reflexivity
    intro x
    exact polar_self_of_singular x.2
  · -- invariance
    intro g x y
    exact perp_pomega_smul g x y
  · -- transitivity
    intro y
    induction y using singularPoints_ind with
    | h v hv hQv =>
    obtain ⟨g, hg, -, c, hc, hgv⟩ := F.exists_move hm hnd (J := ∅) (i := i0) (k := i1)
      (Finset.notMem_empty _) (Finset.notMem_empty _) h01 hv hQv (fun j hj => absurd hj
        (Finset.notMem_empty _))
    exact ⟨_, by rw [hx₀]; exact hpt hg he0 (F.qe i0) hv hQv hc hgv⟩
  · -- the perpendicular suborbit
    intro y y' hy hy' hRy hRy'
    induction y using singularPoints_ind with
    | h v hv hQv =>
    induction y' using singularPoints_ind with
    | h v' hv' hQv' =>
    rw [hx₀, hsperp] at hRy hRy'
    rw [hx₀, Ne] at hy hy'
    -- the components orthogonal to the plane `0`
    have hW : ∀ {v : ι → K} (hv : v ≠ 0) (hQv : Q v = 0) (hRv : polar Q (F.e i0) v = 0)
        (hne : (⟨Projectivization.mk K v hv, mk_mem_singularPoints hv hQv⟩ : singularPoints Q) ≠
          ⟨Projectivization.mk K (F.e i0) he0, mk_mem_singularPoints he0 (F.qe i0)⟩),
        v - polar Q v (F.f i0) • F.e i0 ≠ 0 ∧ Q (v - polar Q v (F.f i0) • F.e i0) = 0 ∧
          F.Perp {i0} (v - polar Q v (F.f i0) • F.e i0) := by
      intro v hv hQv hRv hne
      refine ⟨fun h => hne ?_, ?_, ?_⟩
      · have hv' : v = polar Q v (F.f i0) • F.e i0 := sub_eq_zero.1 h
        have hc : polar Q v (F.f i0) ≠ 0 := fun hc => hv (by rw [hv', hc, zero_smul])
        exact singular_ext (mk_eq_mk_of_eq_smul _ _ hc hv')
      · rw [map_sub_eq, map_smul_eq, F.qe, hQv, polar_smul_right, polar_comm _ v (F.e i0), hRv]
        simp
      · intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_comm, hRv,
          F.ee, F.ef_self]
        simp
    obtain ⟨hvW0, hQvW, hvWJ⟩ := hW hv hQv hRy hy
    obtain ⟨hv'W0, hQv'W, hv'WJ⟩ := hW hv' hQv' hRy' hy'
    set vW := v - polar Q v (F.f i0) • F.e i0
    set v'W := v' - polar Q v' (F.f i0) • F.e i0
    have hnot1 : i1 ∉ ({i0} : Finset (Fin m)) := by simp [Ne.symm h01]
    have hnot2 : i2 ∉ ({i0} : Finset (Fin m)) := by simp [Ne.symm h02]
    obtain ⟨g, hg, hgfix, c, hc, hgv⟩ :=
      F.exists_move hm hnd hnot1 hnot2 h12 hvW0 hQvW hvWJ
    obtain ⟨g', hg', hg'fix, c', hc', hg'v⟩ :=
      F.exists_move hm hnd hnot1 hnot2 h12 hv'W0 hQv'W hv'WJ
    set μ := c⁻¹ * c'
    have hμ : μ ≠ 0 := mul_ne_zero (inv_ne_zero hc) hc'
    set h₁ := g' * g⁻¹
    have hh₁e : h₁ • F.e i0 = F.e i0 := by
      rw [mul_smul, inv_smul_eq_iff.2 (hgfix i0 (Finset.mem_singleton_self _)).symm,
        hg'fix i0 (Finset.mem_singleton_self _)]
    have hh₁v : h₁ • vW = μ • v'W := by
      have : g⁻¹ • vW = c⁻¹ • F.e i1 := by
        rw [inv_smul_eq_iff, gl_smul_smul, hgv, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [mul_smul, this, gl_smul_smul, hg'v, smul_smul]
    -- correct the `e₀`-coordinate with `E(e₀, w)`
    set lam := polar Q v (F.f i0)
    set b' := polar Q v' (F.f i0)
    obtain ⟨w₀, hw₀⟩ := hnd v'W hv'W0
    set w₁ := F.rest {i0} w₀
    have hw₁ : polar Q v'W w₁ ≠ 0 := by rw [F.polar_rest_right _ _ hv'WJ]; exact hw₀
    set t := (lam - μ * b') / μ / polar Q v'W w₁
    set w := t • w₁
    have hew : polar Q (F.e i0) w = 0 := by
      rw [polar_smul_right, polar_comm, F.polar_rest_e _ _ (Finset.mem_singleton_self _),
        smul_zero]
    have hβ : μ * polar Q v'W w = lam - μ * b' := by
      simp only [w, t, polar_smul_right, smul_eq_mul]
      field_simp
    set h₂ := eichGL Q (F.e i0) w
    have hh₂ : h₂ ∈ StatedOmega ⇑Q := F.eichGL_mem hm i0 hew
    have hh₂e : h₂ • F.e i0 = F.e i0 := eichGL_smul_self_vec (F.qe i0) hew
    have hv'W_e : polar Q v'W (F.e i0) = 0 := (hv'WJ i0 (Finset.mem_singleton_self _)).1
    refine ⟨((⟨h₂ * h₁, mul_mem hh₂ (mul_mem hg' (inv_mem hg))⟩ : StatedOmega ⇑Q) :
      StatedProj (StatedOmega ⇑Q)), ?_, ?_⟩
    · rw [hx₀]
      exact hpt _ he0 (F.qe i0) he0 (F.qe i0) one_ne_zero (by
        rw [mul_smul, hh₁e, hh₂e, one_smul])
    · refine hpt _ hv hQv hv' hQv' hμ ?_
      have hv_eq : v = vW + lam • F.e i0 := by simp [vW, lam]
      have hv'_eq : v' = v'W + b' • F.e i0 := by simp [v'W, b']
      rw [mul_smul, hv_eq, gl_smul_add, gl_smul_smul, hh₁e, hh₁v,
        eichGL_smul_eq (F.qe i0) hew, polar_add_left, polar_add_left, polar_smul_left,
        polar_smul_left, polar_smul_left, polar_smul_left, hv'W_e, polar_self_of_singular (F.qe i0),
        hew]
      simp only [smul_eq_mul, mul_zero, add_zero, zero_smul, hβ]
      rw [hv'_eq]
      module
  · -- the non-perpendicular suborbit
    intro y y' hRy hRy'
    induction y using singularPoints_ind with
    | h v hv hQv =>
    induction y' using singularPoints_ind with
    | h v' hv' hQv' =>
    rw [hx₀, hsperp] at hRy hRy'
    have hJ : ∀ v : ι → K, F.Perp ∅ v := fun v j hj => absurd hj (Finset.notMem_empty _)
    have hnot : i0 ∉ (∅ : Finset (Fin m)) := Finset.notMem_empty _
    set c := (polar Q (F.e i0) v)⁻¹
    set c' := (polar Q (F.e i0) v')⁻¹
    have h1 : polar Q (F.e i0) (c • v) = 1 := by
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hRy]
    have h1' : polar Q (F.e i0) (c' • v') = 1 := by
      rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hRy']
    have hQc : Q (c • v) = 0 := by rw [map_smul_eq, hQv, mul_zero]
    have hQc' : Q (c' • v') = 0 := by rw [map_smul_eq, hQv', mul_zero]
    obtain ⟨hg, -, hgv⟩ := F.move_e hm hnot (F.qf i0) hQc (hJ _) (hJ _) (F.ef_self i0) h1
    obtain ⟨hg', -, hg'v⟩ := F.move_e hm hnot (F.qf i0) hQc' (hJ _) (hJ _) (F.ef_self i0) h1'
    set g := eichGL Q (F.e i0) (c • v - F.f i0)
    set g' := eichGL Q (F.e i0) (c' • v' - F.f i0)
    have hge : g • F.e i0 = F.e i0 :=
      eichGL_smul_self_vec (F.qe i0) (by rw [polar_sub_right, h1, F.ef_self, sub_self])
    have hg'e : g' • F.e i0 = F.e i0 :=
      eichGL_smul_self_vec (F.qe i0) (by rw [polar_sub_right, h1', F.ef_self, sub_self])
    refine ⟨((⟨g' * g⁻¹, mul_mem hg' (inv_mem hg)⟩ : StatedOmega ⇑Q) :
      StatedProj (StatedOmega ⇑Q)), ?_, ?_⟩
    · rw [hx₀]
      exact hpt _ he0 (F.qe i0) he0 (F.qe i0) one_ne_zero (by
        rw [mul_smul, inv_smul_eq_iff.2 hge.symm, hg'e, one_smul])
    · have hc : c ≠ 0 := inv_ne_zero hRy
      have hc' : c' ≠ 0 := inv_ne_zero hRy'
      refine hpt _ hv hQv hv' hQv' (mul_ne_zero (inv_ne_zero hc) hc') ?_
      have : g⁻¹ • v = c⁻¹ • F.f i0 := by
        rw [inv_smul_eq_iff, gl_smul_smul, hgv, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [mul_smul, this, gl_smul_smul, hg'v, smul_smul]
  · -- a perpendicular triangle `[e₀], [e₁], [e₀ + e₁]`
    have he1 := F.e_ne_zero i1
    have he01 : F.e i0 + F.e i1 ≠ 0 := fun h => by
      have := congrArg (fun x => polar Q x (F.f i0)) h
      simp only [polar_add_left, F.ef_self, F.ef_ne (Ne.symm h01), polar_zero_left] at this
      norm_num at this
    have hQ01 : Q (F.e i0 + F.e i1) = 0 := by rw [map_add_eq, F.qe, F.qe, F.ee]; ring
    refine ⟨⟨Projectivization.mk K (F.e i1) he1, mk_mem_singularPoints he1 (F.qe i1)⟩,
      ⟨Projectivization.mk K _ he01, mk_mem_singularPoints he01 hQ01⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx₀]
      intro h
      exact mk_ne_mk_of_polar (Q := Q) he1 he0 (w := F.f i1) (by rw [F.ef_self]; exact one_ne_zero)
        (F.ef_ne h01) (congrArg Subtype.val h)
    · rw [hx₀]
      intro h
      exact mk_ne_mk_of_polar (Q := Q) he01 he0 (w := F.f i1)
        (by rw [polar_add_left, F.ef_ne h01, F.ef_self]; norm_num) (F.ef_ne h01)
        (congrArg Subtype.val h)
    · intro h
      exact mk_ne_mk_of_polar (Q := Q) he01 he1 (w := F.f i0)
        (by rw [polar_add_left, F.ef_self, F.ef_ne (Ne.symm h01)]; norm_num)
        (F.ef_ne (Ne.symm h01)) (congrArg Subtype.val h).symm
    · rw [hx₀, hsperp]; exact F.ee _ _
    · rw [hx₀, hsperp, polar_add_right, F.ee, F.ee, add_zero]
    · rw [hsperp, polar_add_right, F.ee, F.ee, add_zero]
  · -- a non-perpendicular triangle `[e₀], [f₀], [e₀ + f₀ + e₁ - f₁]`
    have hf0 := F.f_ne_zero i0
    set x := (F.e i0 + F.f i0) + (F.e i1 - F.f i1)
    have hQx : Q x = 0 := F.Q_hyp h01
    have hxe : polar Q (F.e i0) x = 1 := by
      simp only [x, polar_add_right, polar_sub_right, F.ef_self, F.ee, F.ef_ne h01]; ring
    have hxf : polar Q (F.f i0) x = 1 := by
      simp only [x, polar_add_right, polar_sub_right, F.fe_self, F.ff, F.fe_ne h01]; ring
    have hx0 : x ≠ 0 := fun h => by rw [h, polar_zero_right] at hxe; exact zero_ne_one hxe
    refine ⟨⟨Projectivization.mk K (F.f i0) hf0, mk_mem_singularPoints hf0 (F.qf i0)⟩,
      ⟨Projectivization.mk K x hx0, mk_mem_singularPoints hx0 hQx⟩, ?_, ?_, ?_⟩
    · rw [hx₀, hsperp, F.ef_self]; exact one_ne_zero
    · rw [hx₀, hsperp, hxe]; exact one_ne_zero
    · rw [hsperp, hxf]; exact one_ne_zero

end Frame

end CFSGOutside.HallPaige.Orth
