import CFSGOutside.Arad.Defs

/-!
# Auxiliary lemmas for `PSL(2, F)` (Arad, Lemma 2.1)
-/

open scoped MatrixGroups

namespace CFSGOutside.Arad

variable {F : Type*} [Field F]

/-- Quotient map `SL(2,F) → PSL(2,F)`. -/
abbrev mkP (F : Type*) [Field F] : SL(2, F) →* PSL(2, F) :=
  QuotientGroup.mk' (Subgroup.center SL(2, F))

theorem mkP_surjective : Function.Surjective (mkP F) := QuotientGroup.mk_surjective

theorem mkP_eq_one_iff (A : SL(2, F)) : mkP F A = 1 ↔ A ∈ Subgroup.center SL(2, F) :=
  QuotientGroup.eq_one_iff A

theorem mem_center_of_coe_eq (A : SL(2, F)) (s : F) (h : (A : Matrix (Fin 2) (Fin 2) F) = s • 1) :
    A ∈ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨s, ?_, ?_⟩
  · have := A.2
    rw [h] at this
    simpa [Matrix.det_smul, sq] using this
  · rw [h]; simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_smul_of_mem_center (A : SL(2, F)) (h : A ∈ Subgroup.center SL(2, F)) :
    ∃ s : F, (A : Matrix (Fin 2) (Fin 2) F) = s • 1 ∧ s ^ 2 = 1 := by
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  exact ⟨r, by rw [← hA]; simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply], by simpa using hr⟩

theorem mkP_sq_eq_one (U : SL(2, F)) (s : F) (h : (U : Matrix (Fin 2) (Fin 2) F) ^ 2 = s • 1) :
    mkP F U ^ 2 = 1 := by
  rw [← map_pow, mkP_eq_one_iff]
  exact mem_center_of_coe_eq _ s (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact h)

/-- The Lucas-type sequence `a₀ = 0`, `a₁ = 1`, `aₙ₊₂ = t aₙ₊₁ - aₙ`. -/
def lucas (t : F) : ℕ → F
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * lucas t (n + 1) - lucas t n

theorem sq_eq_trace_smul (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) :
    A ^ 2 = A.trace • A - (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.det_fin_two] at hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination hA | linear_combination -hA

theorem pow_succ_eq (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) (n : ℕ) :
    A ^ (n + 1) = lucas A.trace (n + 1) • A - lucas A.trace n • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two,
      sq_eq_trace_smul A hA]
    simp only [lucas, smul_sub, smul_smul, sub_smul, mul_comm A.trace]
    abel

theorem lucas_two (n : ℕ) : lucas (2 : F) n = n ∧ lucas (2 : F) (n + 1) = (n + 1 : ℕ) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [lucas, ih.2, ih.1]; push_cast; ring

theorem lucas_neg_two (n : ℕ) :
    lucas (-2 : F) n = (-1) ^ (n + 1) * n ∧
      lucas (-2 : F) (n + 1) = (-1) ^ (n + 2) * (n + 1 : ℕ) := by
  induction n with
  | zero => simp [lucas]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [lucas, ih.2, ih.1]; push_cast; ring

theorem eq_char_of_lucas_eq_zero [Finite F] {p : ℕ} (hp : p.Prime) (A : SL(2, F))
    (hA : orderOf (mkP F A) = p)
    (h : lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) (ringChar F) = 0) : p = ringChar F := by
  haveI := Fintype.ofFinite F
  have hc : (ringChar F).Prime := CharP.char_is_prime F _
  obtain ⟨m, hm⟩ : ∃ m, ringChar F = m + 1 := ⟨ringChar F - 1, by have := hc.pos; omega⟩
  have hpow := pow_succ_eq (A : Matrix (Fin 2) (Fin 2) F) A.2 m
  rw [← hm, h, zero_smul, zero_sub, ← neg_smul] at hpow
  have hmem : A ^ ringChar F ∈ Subgroup.center SL(2, F) :=
    mem_center_of_coe_eq _ _ (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact hpow)
  have h1 : mkP F (A ^ ringChar F) = 1 := (mkP_eq_one_iff _).mpr hmem
  rw [map_pow] at h1
  exact (Nat.prime_dvd_prime_iff_eq hp hc).mp (hA ▸ orderOf_dvd_of_pow_eq_one h1)

theorem trace_ne [Finite F] {p : ℕ} (hp : p.Prime) (hpc : p ≠ ringChar F) (A : SL(2, F))
    (hA : orderOf (mkP F A) = p) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 2 ∧
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ -2 := by
  constructor
  · intro h
    refine hpc (eq_char_of_lucas_eq_zero hp A hA ?_)
    rw [h, (lucas_two _).1]; simp
  · intro h
    refine hpc (eq_char_of_lucas_eq_zero hp A hA ?_)
    rw [h, (lucas_neg_two _).1]; simp

theorem bad_of_dihedral {P : Type*} [Group P] (u v : P) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : orderOf (u * v) = p) : Bad P p 2 := by
  have hu' : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← sq, hu]
  have hv' : v⁻¹ = v := by rw [inv_eq_iff_mul_eq_one, ← sq, hv]
  have hconj : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [_root_.mul_inv_rev, hu', hv', ← mul_assoc, ← sq, hu, one_mul]
  have hmap : ∀ y ∈ Subgroup.zpowers (u * v), u * y * u⁻¹ ∈ Subgroup.zpowers (u * v) := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hconj, _root_.inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  refine ⟨Subgroup.zpowers (u * v), ?_, ?_, u, ?_, ?_, 1, by simpa using hu⟩
  · intro h1
    rw [Subgroup.zpowers_eq_bot] at h1
    rw [h1, orderOf_one] at h
    exact hp.one_lt.ne h
  · apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, h, pow_one]
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmap x hx, fun hx => ?_⟩
    have := hmap _ hx
    rwa [hu', ← mul_assoc, ← mul_assoc, ← sq, hu, one_mul, mul_assoc, ← sq, hu, mul_one] at this
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    have h1 := hc (u * v) (Subgroup.mem_zpowers _)
    have h3 : (u * v)⁻¹ = u * v := by
      rw [← hconj, ← h1, mul_inv_cancel_right]
    have h4 : (u * v) ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr h3.symm
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [h] at h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)

/-- The element `!![a, b; c, d]` of `SL(2, F)`. -/
def mk2 (a b c d : F) (h : a * d - b * c = 1) : SL(2, F) :=
  ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two_of] using h⟩

@[simp] theorem coe_mk2 (a b c d : F) (h : a * d - b * c = 1) :
    (mk2 a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

theorem exists_UV [Finite F] (t : F) :
    ∃ U V : SL(2, F), mkP F U ^ 2 = 1 ∧ mkP F V ^ 2 = 1 ∧
      Matrix.trace ((U * V : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = t := by
  haveI := Fintype.ofFinite F
  by_cases hc : ringChar F = 2
  · haveI : CharP F 2 := ringChar.of_eq hc
    have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
    refine ⟨mk2 1 1 0 1 (by ring), mk2 1 0 t 1 (by ring), ?_, ?_, ?_⟩
    · refine mkP_sq_eq_one _ 1 ?_
      ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, h2] <;>
        first | linear_combination h2 | linear_combination t * h2
    · refine mkP_sq_eq_one _ 1 ?_
      ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, h2] <;>
        first | linear_combination h2 | linear_combination t * h2
    · simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, h2]
      linear_combination h2
  · have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C (1 : F) * Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + Polynomial.C 1)
      (g := Polynomial.C (1 : F) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (Polynomial.degree_quadratic one_ne_zero) (Polynomial.degree_quadratic one_ne_zero) hodd
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at hab
    refine ⟨mk2 0 1 (-1) 0 (by ring),
      mk2 b a (a + t) (-b) (by linear_combination -hab), ?_, ?_, ?_⟩
    · refine mkP_sq_eq_one _ (-1) ?_
      ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
    · refine mkP_sq_eq_one _ (-1) ?_
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hab | linear_combination -hab
    · simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]


/-- Case `p ≠ char F` of Arad's Lemma 2.1 for `PSL(2, F)`. -/
theorem bad_of_ne_char [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p ≠ ringChar F)
    (hd : p ∣ Nat.card PSL(2, F)) : Bad PSL(2, F) p 2 := by
  haveI := Fact.mk hp
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨A, rfl⟩ := mkP_surjective y
  obtain ⟨ht2, ht2'⟩ := trace_ne hp hpc A hy
  obtain ⟨U, V, hU, hV, htr⟩ := exists_UV (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F))
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hApow : A ^ p ∈ Subgroup.center SL(2, F) := by
    rw [← mkP_eq_one_iff, map_pow]; exact hy ▸ pow_orderOf_eq_one _
  obtain ⟨s, hs, -⟩ := exists_smul_of_mem_center _ hApow
  have hA1 := pow_succ_eq (A : Matrix (Fin 2) (Fin 2) F) A.2 m
  have hB1 := pow_succ_eq ((U * V : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) (U * V).2 m
  rw [htr, ← hm] at hB1
  rw [← hm] at hA1
  rw [Matrix.SpecialLinearGroup.coe_pow] at hs
  rw [hs] at hA1
  have hlp : lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) p = 0 := by
    by_contra hne
    have hAc : A ∈ Subgroup.center SL(2, F) := by
      refine mem_center_of_coe_eq A ((lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) p)⁻¹ *
        (s + lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) m)) ?_
      have : lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) p • (A : Matrix (Fin 2) (Fin 2) F) =
          (s + lucas (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) m) • 1 := by
        rw [add_smul, hA1]; abel
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have := (mkP_eq_one_iff A).mpr hAc
    rw [this, orderOf_one] at hy
    exact hp.one_lt.ne hy
  have hBp : (U * V) ^ p = A ^ p := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, hB1, hs, hlp]
    rw [hlp] at hA1
    simpa using hA1.symm
  have hord : orderOf (mkP F (U * V)) = p := by
    apply orderOf_eq_prime
    · rw [← map_pow, hBp, map_pow, ← hy]; exact pow_orderOf_eq_one _
    · rw [Ne, mkP_eq_one_iff]
      intro hc
      obtain ⟨r, hr, hr2⟩ := exists_smul_of_mem_center _ hc
      have htr' : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = r * 2 := by
        rw [← htr, hr]; simp [Matrix.trace_fin_two]
      have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
      rcases mul_eq_zero.mp this with h | h
      · exact ht2 (by rw [htr', show r = 1 by linear_combination h]; ring)
      · exact ht2' (by rw [htr', show r = -1 by linear_combination h]; ring)
  rw [map_mul] at hord
  exact bad_of_dihedral _ _ hU hV hp hp2 hord


/-- The transvection `!![1, b; 0, 1]`. -/
def uni (b : F) : SL(2, F) := mk2 1 b 0 1 (by ring)

@[simp] theorem coe_uni (b : F) : (uni b : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl

theorem uni_add (a b : F) : uni (a + b) = uni a * uni b := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, add_comm]

/-- The diagonal matrix `diag(d, d⁻¹)`. -/
def Dm : Fˣ →* SL(2, F) where
  toFun d := mk2 d 0 0 (d⁻¹ : Fˣ) (by simp)
  map_one' := by apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, mul_comm]

theorem coe_Dm (d : Fˣ) :
    (Dm d : Matrix (Fin 2) (Fin 2) F) = !![(d : F), 0; 0, ((d⁻¹ : Fˣ) : F)] := rfl

theorem Dm_mul_uni (d : Fˣ) (b : F) : Dm d * uni b = uni ((d : F) ^ 2 * b) * Dm d := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_Dm] <;> field_simp


/-- The unipotent subgroup of `PSL(2, F)` as the image of `Multiplicative F`. -/
def Uhom (F : Type*) [Field F] : Multiplicative F →* PSL(2, F) :=
  MonoidHom.mk' (fun b => mkP F (uni (Multiplicative.toAdd b)))
    (fun a b => by simp [uni_add])

theorem Uhom_eq_one_iff (b : F) : Uhom F (Multiplicative.ofAdd b) = 1 ↔ b = 0 := by
  change mkP F (uni b) = 1 ↔ _
  rw [mkP_eq_one_iff]
  constructor
  · intro h
    obtain ⟨s, hs, -⟩ := exists_smul_of_mem_center _ h
    have := congrFun (congrFun hs 0) 1
    simpa using this
  · rintro rfl
    exact mem_center_of_coe_eq _ 1 (by ext i j; fin_cases i <;> fin_cases j <;> simp)

theorem Uhom_injective : Function.Injective (Uhom F) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  exact congrArg Multiplicative.ofAdd ((Uhom_eq_one_iff (Multiplicative.toAdd b)).mp hb)

theorem conj_Uhom (d : Fˣ) (b : F) :
    mkP F (Dm d) * Uhom F (Multiplicative.ofAdd b) * (mkP F (Dm d))⁻¹ =
      Uhom F (Multiplicative.ofAdd ((d : F) ^ 2 * b)) := by
  rw [mul_inv_eq_iff_eq_mul]
  change mkP F (Dm d) * mkP F (uni b) = mkP F (uni _) * mkP F (Dm d)
  rw [← map_mul, ← map_mul, Dm_mul_uni]
  rfl

theorem mkP_Dm_eq_one (e : Fˣ) (he : e ^ 2 = 1) : mkP F (Dm e) = 1 := by
  rw [mkP_eq_one_iff]
  have : e⁻¹ = e := by
    rw [inv_eq_iff_mul_eq_one, ← sq, he]
  refine mem_center_of_coe_eq _ (e : F) ?_
  rw [coe_Dm, this]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- Case `p = char F` of Arad's Lemma 2.1 for `PSL(2, F)`. -/
theorem bad_of_char [Finite F] {p : ℕ} (hp : p.Prime) (hpc : p = ringChar F) (d : Fˣ)
    (hd : d ^ 2 ≠ 1) {s k : ℕ} (hdk : (d ^ s ^ k) ^ 2 = 1) : Bad PSL(2, F) p s := by
  haveI := Fintype.ofFinite F
  have hpg : IsPGroup p (Multiplicative F) := by
    haveI : CharP F p := hpc ▸ ringChar.charP F
    haveI := Fact.mk hp
    obtain ⟨n, -, hn⟩ := FiniteField.card F p
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), Nat.card_eq_fintype_card]
    exact hn
  refine ⟨(Uhom F).range, ?_, ?_, mkP F (Dm d), ?_, ?_, k, ?_⟩
  · intro h
    have : Uhom F (Multiplicative.ofAdd 1) ∈ (Uhom F).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, Uhom_eq_one_iff] at this
    exact one_ne_zero this
  · exact hpg.of_surjective (Uhom F).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨Multiplicative.ofAdd ((d : F) ^ 2 * Multiplicative.toAdd b), ?_⟩
      rw [← conj_Uhom]; rfl
    · rintro ⟨b, hb⟩
      refine ⟨Multiplicative.ofAdd (((d⁻¹ : Fˣ) : F) ^ 2 * Multiplicative.toAdd b), ?_⟩
      have := conj_Uhom d⁻¹ (Multiplicative.toAdd b)
      simp only [map_inv, inv_inv, ofAdd_toAdd] at this
      rw [← this, hb]; group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    have h1 := hc (Uhom F (Multiplicative.ofAdd 1)) ⟨_, rfl⟩
    have h2 := conj_Uhom d 1
    rw [mul_inv_eq_iff_eq_mul, ← h1] at h2
    have h3 := Uhom_injective (by simpa using h2.symm)
    apply hd
    apply Units.ext
    have h4 := (Multiplicative.ofAdd.injective h3).symm
    simpa using h4.symm
  · rw [← map_pow, ← map_pow]
    exact mkP_Dm_eq_one _ hdk

theorem card_rootsOfUnity_two (F : Type*) [Field F] [Finite F] (h : Odd (Nat.card F)) :
    Nat.card (rootsOfUnity 2 F) = 2 := by
  have hc : ringChar F ≠ 2 := by
    haveI := Fintype.ofFinite F
    intro h2
    have := (FiniteField.even_card_iff_char_two (F := F)).mp h2
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := h
    omega
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h1
    have := congrArg Units.val h1
    simp at this
    exact Ring.neg_one_ne_one_of_char_ne_two hc this
  have : (rootsOfUnity 2 F : Set Fˣ) = {1, -1} := by
    ext x
    simp only [SetLike.mem_coe, mem_rootsOfUnity, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hx' : x * x = 1 := by simpa [sq] using hx
      have := mul_self_eq_one_iff.mp (congrArg Units.val hx')
      rcases this with h | h
      · left; exact Units.ext (by simpa using h)
      · right; exact Units.ext (by simpa using h)
    · rintro (rfl | rfl) <;> simp
  have h2 : Nat.card (rootsOfUnity 2 F) = Nat.card ((rootsOfUnity 2 F : Set Fˣ)) := rfl
  rw [h2, this, Nat.card_coe_set_eq, Set.ncard_pair hne.symm]

theorem card_psl_aux (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    Nat.card PSL(2, F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  haveI := Fintype.ofFinite F
  classical
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field] at h1
  have hu : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_units]
  have hcen : Nat.card (Subgroup.center SL(2, F)) = 2 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F)).toEquiv]
    simpa using card_rootsOfUnity_two F hF
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  rw [hcen] at h3
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    ← Nat.card_eq_fintype_card] at h1
  rw [hu] at h1
  have hq : 3 ≤ Nat.card F := by
    obtain ⟨k, hk⟩ := hF
    have := Finite.one_lt_card (α := F)
    omega
  obtain ⟨n, hn⟩ : ∃ n, Nat.card F = n + 3 := ⟨Nat.card F - 3, by omega⟩
  change Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) * 2 = _
  rw [← h3]
  rw [hn] at h1 ⊢
  have h4 : (n + 2) * Nat.card SL(2, F) = (n + 3) * ((n + 3) ^ 2 - 1) * (n + 2) := by
    have : (n + 3) ^ 2 - 1 = (n + 2) * (n + 4) := by
      rw [show (n + 3) ^ 2 = (n + 2) * (n + 4) + 1 by ring]; simp
    have h5 : (n + 3) ^ 2 - (n + 3) = (n + 3) * (n + 2) := by
      rw [show (n + 3) ^ 2 = (n + 3) * (n + 2) + (n + 3) by ring]; simp
    rw [this]
    rw [h5, show n + 3 - 1 = n + 2 by omega] at h1
    nlinarith [h1]
  have h5 : Nat.card SL(2, F) = (n + 3) * ((n + 3) ^ 2 - 1) :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 2) (by rw [h4]; ring)
  exact h5

end CFSGOutside.Arad
