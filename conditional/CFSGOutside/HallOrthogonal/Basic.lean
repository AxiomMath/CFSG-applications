import CFSGOutside.HallOrthogonal.Defs
import CFSGOutside.Corpus.ReflectMulReflectClosure
import CFSGOutside.Corpus.Defs.ZSReflectionGroups

/-!
# Hall (2008), Theorem 1.1, orthogonal case: reflections

Over a field of characteristic not two with a nondegenerate quadratic form `Q`, the reflections of Hall (drop `1`
and determinant `-1`), the reflections `IsRefl` of Zalesskiĭ–Serežkin that are isometries (`t² = 1` and
`rank (t - 1) = 1`), and the maps `x ↦ x - (⟨v, x⟩ / Q v) v` with `Q v ≠ 0` are the same.
-/

namespace CFSGOutside.HallOrthogonal

open Module QuadraticMap
open CFSGOutside.Corpus.ClassicalGroups.Orthogonal (reflect)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Reflect

variable (Q : QuadraticForm K V)

theorem reflect_apply {v : V} (hv : Q v ≠ 0) (x : V) :
    reflect Q v x = x - (polar Q v x / Q v) • v := by
  letI : Invertible (Q v) := invertibleOfNonzero hv
  simp only [reflect, dif_pos hv]
  exact TauCeti.QuadraticMap.reflection_apply_eq_sub_div Q v x

theorem reflect_of_eq_zero {v : V} (hv : Q v = 0) : reflect Q v = 1 := by
  simp [reflect, hv]

theorem reflect_mem (v : V) : reflect Q v ∈ orthGroup Q := by
  by_cases hv : Q v = 0
  · rw [reflect_of_eq_zero Q hv]
    exact (orthGroup Q).one_mem
  · letI : Invertible (Q v) := invertibleOfNonzero hv
    simp only [reflect, dif_pos hv]
    exact TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v

theorem polar_self_eq (x : V) : polar Q x x = 2 * Q x := by
  rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat]

theorem reflect_apply_self {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply Q hv, polar_self_eq, mul_div_cancel_right₀ _ hv, two_smul]
  abel

theorem reflect_mul_self (v : V) : reflect Q v * reflect Q v = 1 := by
  by_cases hv : Q v = 0
  · rw [reflect_of_eq_zero Q hv, one_mul]
  · refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, reflect_apply Q hv (reflect Q v x), reflect_apply Q hv x,
      polar_sub_right, polar_smul_right, polar_self_eq, smul_eq_mul]
    change _ = x
    have : polar Q v x - polar Q v x / Q v * (2 * Q v) = -polar Q v x := by
      field_simp
      ring
    rw [this, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem reflect_inv (v : V) : (reflect Q v)⁻¹ = reflect Q v :=
  inv_eq_of_mul_eq_one_left (reflect_mul_self Q v)

theorem reflect_smul {c : K} (hc : c ≠ 0) (v : V) : reflect Q (c • v) = reflect Q v := by
  by_cases hv : Q v = 0
  · rw [reflect_of_eq_zero Q hv, reflect_of_eq_zero Q (by rw [QuadraticMap.map_smul, hv,
      smul_zero])]
  · have hcv : Q (c • v) ≠ 0 := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
      exact mul_ne_zero (mul_ne_zero hc hc) hv
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply Q hcv, reflect_apply Q hv, QuadraticMap.map_smul, polar_smul_left,
      smul_eq_mul, smul_eq_mul, smul_smul]
    congr 2
    field_simp

variable {Q} in
theorem reflect_conj {g : V ≃ₗ[K] V} (hg : g ∈ orthGroup Q) (v : V) :
    g * reflect Q v * g⁻¹ = reflect Q (g v) := by
  by_cases hv : Q v = 0
  · rw [reflect_of_eq_zero Q hv, reflect_of_eq_zero Q
      (by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hv]), mul_one, mul_inv_cancel]
  · have hgv : Q (g v) ≠ 0 := by rwa [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg]
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply Q hv, reflect_apply Q hgv,
      map_sub, map_smul, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg,
      ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg v (g⁻¹ x)]
    have : g (g⁻¹ x) = x := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [this]

theorem reflect_sub_id_apply {v : V} (hv : Q v ≠ 0) (x : V) :
    (((reflect Q v).toLinearMap - LinearMap.id : V →ₗ[K] V) x) = -(polar Q v x / Q v) • v := by
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, reflect_apply Q hv, LinearMap.id_apply, neg_smul]
  abel

theorem range_reflect_sub_id (h2 : (2 : K) ≠ 0) {v : V} (hv : Q v ≠ 0) :
    LinearMap.range ((reflect Q v).toLinearMap - LinearMap.id : V →ₗ[K] V) = K ∙ v := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [reflect_sub_id_apply Q hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨-(1 / 2 : K) • v, ?_⟩
    rw [reflect_sub_id_apply Q hv]
    have : -(polar Q v (-(1 / 2 : K) • v) / Q v) = 1 := by
      rw [polar_smul_right, polar_self_eq, smul_eq_mul]
      field_simp
    rw [this, one_smul]

end Reflect


section Characterize

variable {Q : QuadraticForm K V}

/-- A linear map whose difference with the identity has rank one is `x ↦ x + φ x • a`. -/
theorem exists_rankOne [FiniteDimensional K V] (t : V →ₗ[K] V)
    (h : finrank K (LinearMap.range (t - LinearMap.id)) = 1) :
    ∃ (a : V) (φ : Dual K V), a ≠ 0 ∧ φ ≠ 0 ∧ ∀ x, t x = x + φ x • a := by
  set W := LinearMap.range (t - LinearMap.id)
  let b : Basis (Fin 1) K W := Module.finBasisOfFinrankEq K W h
  let φ : Dual K V := (b.coord 0).comp (t - LinearMap.id).rangeRestrict
  have hx : ∀ x, t x = x + φ x • (b 0 : V) := by
    intro x
    have h1 := b.sum_repr ((t - LinearMap.id).rangeRestrict x)
    rw [Fintype.sum_unique] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_smul, LinearMap.codRestrict_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h2
    have : (default : Fin 1) = 0 := rfl
    rw [this] at h2
    change t x = x + (b.repr ((t - LinearMap.id).rangeRestrict x) 0) • (b 0 : V)
    rw [h2]
    abel
  refine ⟨b 0, φ, fun h0 => b.ne_zero 0 (Subtype.ext h0), fun hφ => ?_, hx⟩
  have hW : W = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_bot, LinearMap.sub_apply, hx x, hφ, LinearMap.zero_apply, zero_smul,
      add_zero, LinearMap.id_apply, sub_self]
  rw [hW, finrank_bot] at h
  exact absurd h (by norm_num)

theorem finrank_range_of_drop [FiniteDimensional K V] {g : V ≃ₗ[K] V} (hg : drop g = 1) :
    finrank K (LinearMap.range ((g : V →ₗ[K] V) - LinearMap.id)) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((g : V →ₗ[K] V) - LinearMap.id)
  have hle : finrank K (fixSpace g) ≤ finrank K V := Submodule.finrank_le _
  unfold drop at hg
  change _ + finrank K (fixSpace g) = _ at h
  omega

theorem drop_of_finrank_range [FiniteDimensional K V] {g : V ≃ₗ[K] V}
    (hg : finrank K (LinearMap.range ((g : V →ₗ[K] V) - LinearMap.id)) = 1) : drop g = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((g : V →ₗ[K] V) - LinearMap.id)
  unfold drop
  change _ + finrank K (fixSpace g) = _ at h
  omega

/-- An isometry `x ↦ x + φ x • a` with `φ a = -2` is the reflection in `a`. -/
theorem eq_reflect (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ orthGroup Q) {a : V} (ha : a ≠ 0) {φ : Dual K V} (hφa : φ a = -2)
    (htx : ∀ x, t x = x + φ x • a) : Q a ≠ 0 ∧ t = reflect Q a := by
  have hta : t a = -a := by
    rw [htx, hφa]
    module
  have key : ∀ x, φ x * Q a = -polar Q x a := by
    intro x
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht x a
    rw [htx, hta, polar_neg_right, polar_add_left, polar_smul_left, polar_self_eq,
      smul_eq_mul] at h1
    have : (2 : K) * (φ x * Q a) = 2 * (-polar Q x a) := by linear_combination -h1
    exact mul_left_cancel₀ h2 this
  have hQa : Q a ≠ 0 := by
    intro h0
    apply ha
    apply hQ.1 a
    intro y
    have := key y
    rw [h0, mul_zero, zero_eq_neg] at this
    rw [polarBilin_apply_apply, polar_comm]
    exact this
  refine ⟨hQa, LinearEquiv.ext fun x => ?_⟩
  rw [htx, reflect_apply Q hQa, sub_eq_add_neg, ← neg_smul]
  congr 2
  rw [polar_comm]
  field_simp
  linear_combination key x

theorem det_reflect [FiniteDimensional K V] {a : V} (ha : Q a ≠ 0) :
    LinearEquiv.det (reflect Q a) = -1 := by
  let φ : Dual K V := -(1 / Q a) • polarBilin Q a
  have hcoe : (reflect Q a : V →ₗ[K] V) = LinearMap.transvection φ a := by
    ext x
    rw [LinearEquiv.coe_coe, reflect_apply Q ha, LinearMap.transvection.apply]
    simp only [φ, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 1
    ring_nf
  apply Units.ext
  rw [LinearEquiv.coe_det, hcoe, LinearMap.transvection.det]
  simp only [φ, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul, polar_self_eq,
    Units.val_neg, Units.val_one]
  field_simp
  ring

/-- Hall's reflections are the reflections in non-isotropic vectors. -/
theorem isReflection_iff [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V} :
    IsReflection Q g ↔ ∃ a, Q a ≠ 0 ∧ g = reflect Q a := by
  constructor
  · rintro ⟨hgO, hdrop, hdet⟩
    obtain ⟨a, φ, ha, -, hx⟩ := exists_rankOne (g : V →ₗ[K] V) (finrank_range_of_drop hdrop)
    replace hx : ∀ x, g x = x + φ x • a := fun x => hx x
    have hcoe : (g : V →ₗ[K] V) = LinearMap.transvection φ a := by
      ext x
      rw [LinearMap.transvection.apply, LinearEquiv.coe_coe, hx]
    have hφa : φ a = -2 := by
      have := congrArg (fun u : Kˣ => (u : K)) hdet
      simp only [LinearEquiv.coe_det, hcoe, LinearMap.transvection.det, Units.val_neg,
        Units.val_one] at this
      linear_combination this
    obtain ⟨hQa, hg⟩ := eq_reflect h2 hQ hgO ha hφa hx
    exact ⟨a, hQa, hg⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨reflect_mem Q a, drop_of_finrank_range ?_, det_reflect ha⟩
    change finrank K (LinearMap.range ((reflect Q a).toLinearMap - LinearMap.id : V →ₗ[K] V)) = 1
    rw [range_reflect_sub_id Q h2 ha, finrank_span_singleton]
    intro h0
    apply ha
    rw [h0, QuadraticMap.map_zero]

/-- The reflections of Zalesskiĭ–Serežkin (`t² = 1`, `rank (t - 1) = 1`) in `O(V)`. -/
theorem isInvRankOne_iff [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V} (ht : t ∈ orthGroup Q) :
    (t * t = 1 ∧ finrank K (LinearMap.range ((t : V →ₗ[K] V) - LinearMap.id)) = 1) ↔
      ∃ a, Q a ≠ 0 ∧ t = reflect Q a := by
  constructor
  · rintro ⟨htt, hr⟩
    obtain ⟨a, φ, ha, hφ, hx⟩ := exists_rankOne (t : V →ₗ[K] V) hr
    replace hx : ∀ x, t x = x + φ x • a := fun x => hx x
    have hφa : φ a = -2 := by
      obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hφ (LinearMap.ext hc)
      have h1 : t (t y) = y := by
        have := congrArg (fun f : V ≃ₗ[K] V => f y) htt
        simpa using this
      rw [hx (t y), hx y, map_add, map_smul, smul_eq_mul, add_assoc, ← add_smul] at h1
      have h3 : (φ y + (φ y + φ y * φ a)) • a = 0 := by
        have := congrArg (· - y) h1
        simpa using this
      rcases smul_eq_zero.mp h3 with h | h
      · have : φ y * (2 + φ a) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hy
        · linear_combination h'
      · exact absurd h ha
    obtain ⟨hQa, hg⟩ := eq_reflect h2 hQ ht ha hφa hx
    exact ⟨a, hQa, hg⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨reflect_mul_self Q a, ?_⟩
    change finrank K (LinearMap.range ((reflect Q a).toLinearMap - LinearMap.id : V →ₗ[K] V)) = 1
    rw [range_reflect_sub_id Q h2 ha, finrank_span_singleton]
    intro h0
    apply ha
    rw [h0, QuadraticMap.map_zero]

end Characterize

end CFSGOutside.HallOrthogonal
