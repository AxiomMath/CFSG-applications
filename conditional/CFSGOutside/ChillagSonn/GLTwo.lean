import Mathlib

/-!
# Two-dimensional linear algebra for Lemma (1.9) of Chillag–Sonn

`Aut` of an elementary abelian group of order `r²` embeds in `GL(2, 𝔽_r)`; involutions in
`SL(2, K)` are `±1`; perfect subgroups of `GL` lie in `SL`; and `GL(2, 𝔽_r) → PSL(2, 𝔽_{r²})`.
-/

open scoped MatrixGroups

namespace CFSGOutside.ChillagSonn

/-- The automorphism group of an abelian group of order `r²` and exponent `r` embeds in `GL(2, 𝔽_r)`. -/
theorem exists_injective_mulAut_to_GL {W : Type} [Group W] [Finite W] {r : ℕ} [Fact r.Prime]
    (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ x : W, x ^ r = 1) (hcard : Nat.card W = r ^ 2) :
    ∃ ρ : MulAut W →* GL (Fin 2) (ZMod r), Function.Injective ρ := by
  let : CommGroup W := { mul_comm := hcomm }
  let : Module (ZMod r) (Additive W) := AddCommGroup.zmodModule (n := r) fun x => hexp x.toMul
  have hr := (Fact.out : r.Prime)
  have : Module.Finite (ZMod r) (Additive W) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod r) (Additive W) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := Additive W)
    rw [Nat.card_zmod, show Nat.card (Additive W) = Nat.card W from rfl, hcard] at h
    exact (Nat.pow_right_injective hr.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod r) (Additive W) hfr
  let φ : MulAut W →* Module.End (ZMod r) (Additive W) :=
    { toFun e := (MulEquiv.toAdditive e).toAddMonoidHom.toZModLinearMap r
      map_one' := rfl
      map_mul' _ _ := rfl }
  refine ⟨(Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp φ.toHomUnits, ?_⟩
  intro e e' h
  have h1 := Units.map_injective (LinearMap.toMatrixAlgEquiv b).injective h
  ext x
  exact congrArg Additive.toMul (LinearMap.congr_fun (congrArg Units.val h1) (Additive.ofMul x))

/-- An element of `SL(2, K)` (`K` a field of characteristic `≠ 2`) of order dividing 2 is `±1`. -/
theorem eq_one_or_eq_neg_one_of_sq_eq_one {K : Type} [Field K] (hK : ringChar K ≠ 2) (g : GL (Fin 2) K)
    (hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1) (hg : g ^ 2 = 1) : g = 1 ∨ g = -1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hm : (g : Matrix (Fin 2) (Fin 2) K) * g = 1 := by
    simpa [sq] using congrArg Units.val hg
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * g) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by rw [hm]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at h00 h01 h10 h11
  simp only [Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero]
    at h00 h01 h10 h11
  set a := (g : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) K) 1 1
  have htr : a + d ≠ 0 := by
    intro h
    apply h2
    have : d = -a := by linear_combination h
    rw [this] at hdet
    linear_combination -hdet - h00
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    simpa [htr] using this
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    simpa [htr] using this
  have had : d = a := by
    have : (a - d) * (a + d) = 0 := by linear_combination h00 - h11
    linear_combination -(mul_eq_zero.mp this).resolve_right htr
  have ha : a = 1 ∨ a = -1 :=
    mul_self_eq_one_iff.mp (by rw [hb, zero_mul, add_zero] at h00; exact h00)
  have key : ∀ i j,
      (g : Matrix (Fin 2) (Fin 2) K) i j = a * (1 : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, b, c, d, hb, hc, had] <;> rfl
  rcases ha with ha | ha
  · left; ext i j; simpa [ha] using key i j
  · right; ext i j; simpa [ha] using key i j

/-- A perfect subgroup of `GL(n, K)` lies in `SL(n, K)`. -/
theorem det_eq_one_of_perfect {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (H : Subgroup (GL n K)) (hH : commutator H = ⊤) (g : GL n K) (hg : g ∈ H) :
    (g : Matrix n n K).det = 1 := by
  have := Abelianization.commutator_subset_ker
    ((Matrix.GeneralLinearGroup.det : GL n K →* Kˣ).comp H.subtype)
    (hH.symm ▸ Subgroup.mem_top (⟨g, hg⟩ : H))
  simpa [Units.ext_iff] using this

/-- `GL(2, 𝔽_r) → PSL(2, 𝔽_{r²})`, with kernel the scalar matrices. -/
theorem exists_hom_GL_to_PSL_sq (r : ℕ) [Fact r.Prime] (hr2 : r ≠ 2) :
    ∃ f : GL (Fin 2) (ZMod r) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField r 2),
      ∀ g : GL (Fin 2) (ZMod r), f g = 1 ↔ ∃ c : (ZMod r)ˣ, g = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  set F := GaloisField r 2
  have hr := (Fact.out : r.Prime)
  let : Fintype F := Fintype.ofFinite F
  let φ : ZMod r →+* F := algebraMap (ZMod r) F
  have hF : ringChar F ≠ 2 := by rwa [ringChar.eq F r]
  have hcard : Fintype.card F = r ^ 2 := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card r 2 two_ne_zero
  have hsq : ∀ u : (ZMod r)ˣ, IsSquare (φ u) := fun u => by
    have hu : φ u ≠ 0 := (map_ne_zero φ).mpr u.ne_zero
    rw [FiniteField.isSquare_iff hF hu, hcard]
    obtain ⟨k, rfl⟩ := hr.odd_of_ne_two hr2
    have : (2 * k + 1) ^ 2 / 2 = (2 * k + 1 - 1) * (k + 1) := by
      rw [show (2 * k + 1) ^ 2 = 1 + 2 * (2 * k * (k + 1)) by ring, Nat.add_mul_div_left _ _ two_pos,
        Nat.add_sub_cancel]
      norm_num [mul_assoc]
    rw [this, pow_mul, ← map_pow, ZMod.pow_card_sub_one_eq_one u.ne_zero, map_one, one_pow]
  let M := Matrix.GeneralLinearGroup.map (n := Fin 2) φ
  let P := Matrix.ProjGenLinGroup.mk.comp M
  have hP : ∀ g, P g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro g
    obtain ⟨t, ht⟩ := hsq (Matrix.GeneralLinearGroup.det g)⁻¹
    have ht0 : t ≠ 0 := by
      rintro rfl; rw [mul_zero] at ht; exact (map_ne_zero φ).mpr (Units.ne_zero _) ht
    have hdet : ((t • (M g : Matrix (Fin 2) (Fin 2) F)).det) = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply,
        Matrix.GeneralLinearGroup.map_det, sq, ← ht, Units.coe_map]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, Matrix.GeneralLinearGroup.val_det_apply]
      exact inv_mul_cancel₀ ((map_ne_zero φ).mpr
        (by simpa using (Matrix.GeneralLinearGroup.det g).ne_zero))
    refine ⟨QuotientGroup.mk ⟨_, hdet⟩, ?_⟩
    refine Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨(Units.mk0 t ht0)⁻¹, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val, Units.val_mk0]
    change (t • (M g : Matrix (Fin 2) (Fin 2) F)) * _ = _
    rw [Matrix.smul_mul, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, mul_inv_cancel₀ ht0, one_smul]
  let e := MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
  refine ⟨e.symm.toMonoidHom.comp (P.codRestrict _ hP), fun g => ?_⟩
  have hM : Function.Injective M := fun x y h =>
    Units.ext (Matrix.map_injective φ.injective (congrArg Units.val h))
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, map_one,
    Subtype.ext_iff, MonoidHom.codRestrict_apply, OneMemClass.coe_one]
  simp only [P, MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one]
  constructor
  · intro h
    have : g ∈ Subgroup.center (GL (Fin 2) (ZMod r)) := Subgroup.mem_center_iff.mpr fun y =>
      hM (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp h (M y))
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    rw [Matrix.GeneralLinearGroup.map_scalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩

end CFSGOutside.ChillagSonn
