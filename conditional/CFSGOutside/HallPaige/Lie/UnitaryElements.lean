import CFSGOutside.HallPaige.Lie.UnitaryForm

/-!
# Unitary transvections, Eichler transformations and isotropic vectors

Ported (proofs copied) from AxiomMath/CFSG @ 69cb972, CFSG/ClassicalGroups/Unitary/Elements.lean,
CFSG/ClassicalGroups/Unitary/IsotropicPerp.lean and `exists_fix_smul_eq`,
`exists_fix_herm_ne_zero` of CFSG/ClassicalGroups/Unitary/Action.lean. No corpus axioms.
-/

namespace CFSGOutside.HallPaige.Unitary

open Matrix

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

variable (σ) in
noncomputable def tvMat (a : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + c • vecMulVec a (fun i => σ (a i))

theorem tvMat_mulVec (a : Fin n → K) (c : K) (v : Fin n → K) :
    tvMat σ a c *ᵥ v = v + (c * herm σ a v) • a := by
  rw [tvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem tvMat_det {a : Fin n → K} (ha : herm σ a a = 0) (c : K) : (tvMat σ a c).det = 1 := by
  rw [tvMat, ← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, smul_eq_mul]
  have : (fun i => σ (a i)) ⬝ᵥ a = herm σ a a := rfl
  rw [this, ha, mul_zero, add_zero]

theorem tvMat_isometry (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (x y : Fin n → K) :
    herm σ (tvMat σ a c *ᵥ x) (tvMat σ a c *ᵥ y) = herm σ x y := by
  rw [tvMat_mulVec, tvMat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, map_mul,
    mul_zero, add_zero]
  rw [herm_conj σ hσ a x]
  linear_combination σ (herm σ a x) * herm σ a y * hc

noncomputable def tv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0)
    {c : K} (hc : c + σ c = 0) : SUid σ n :=
  mkSU σ (tvMat σ a c) (tvMat_det ha c) (tvMat_isometry hσ ha hc)

theorem tv_smul (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (v : Fin n → K) : tv hσ ha hc • v = v + (c * herm σ a v) • a :=
  tvMat_mulVec a c v

variable (σ n) in
def tvSet : Set (SUid σ n) :=
  {g | ∃ (a : Fin n → K) (c : K), herm σ a a = 0 ∧ c + σ c = 0 ∧
    ∀ v, g • v = v + (c * herm σ a v) • a}

variable (σ n) in
def T : Subgroup (SUid σ n) := Subgroup.closure (tvSet σ n)

noncomputable def eichlerMat (σ : K ≃+* K) (e y : Fin n → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  (1 + vecMulVec (y + c • e) (fun i => σ (e i))) * (1 + vecMulVec (-e) (fun i => σ (y i)))

theorem eichlerMat_mulVec {e y : Fin n → K} (he : herm σ e e = 0) (c : K) (x : Fin n → K) :
    eichlerMat σ e y c *ᵥ x = x + herm σ e x • (y + c • e) - herm σ y x • e := by
  rw [eichlerMat, ← Matrix.mulVec_mulVec]
  have h1 : ∀ (u : Fin n → K) (w : Fin n → K) (z : Fin n → K),
      (1 + vecMulVec u (fun i => σ (w i))) *ᵥ z = z + herm σ w z • u := by
    intro u w z
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rfl
  rw [h1, h1]
  simp only [herm_add_right, herm_smul_right, herm_neg_right, he, mul_zero, neg_zero, add_zero]
  module

theorem eichlerMat_det (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) (c : K) : (eichlerMat σ e y c).det = 1 := by
  rw [eichlerMat, Matrix.det_mul, Matrix.vecMulVec_eq (Fin 1), Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have e1 : (fun i => σ (e i)) ⬝ᵥ (y + c • e) = herm σ e (y + c • e) := rfl
  have e2 : (fun i => σ (y i)) ⬝ᵥ (-e) = herm σ y (-e) := rfl
  rw [e1, e2, herm_add_right, herm_smul_right, he, hey, herm_neg_right,
    herm_eq_zero_comm σ hσ hey]
  ring

theorem eichler_isometry (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) (x x' : Fin n → K) :
    herm σ (x + herm σ e x • (y + c • e) - herm σ y x • e)
      (x' + herm σ e x' • (y + c • e) - herm σ y x' • e) = herm σ x x' := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  simp only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, herm_smul_left,
    herm_smul_right, he, hey, hye, mul_zero, add_zero, sub_zero]
  simp only [herm_conj σ hσ e x, herm_conj σ hσ x y, hσ]
  linear_combination σ (herm σ e x) * herm σ e x' * hc

noncomputable def eichler (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K}
    (he : herm σ e e = 0) (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) :
    SUid σ n :=
  mkSU σ (eichlerMat σ e y c) (eichlerMat_det hσ he hey c) (fun x x' => by
    rw [eichlerMat_mulVec he, eichlerMat_mulVec he]
    exact eichler_isometry hσ he hey hc x x')

theorem eichler_smul (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) (x : Fin n → K) :
    eichler hσ he hey hc • x = x + herm σ e x • (y + c • e) - herm σ y x • e :=
  eichlerMat_mulVec he c x

theorem eichler_smul_self (hσ : ∀ c, σ (σ c) = c) {e y : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) {c : K} (hc : c + σ c = -herm σ y y) :
    eichler hσ he hey hc • e = e := by
  rw [eichler_smul, he, herm_eq_zero_comm σ hσ hey, zero_smul, zero_smul, add_zero, sub_zero]

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

private lemma exists_iso_of_herm_ne_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {e v : Fin n → K} (he : herm σ e e = 0) (hev : herm σ e v ≠ 0) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_isotropize hσ he (y := (herm σ e v)⁻¹ • v)
    (by rw [herm_smul_right, inv_mul_cancel₀ hev])
  set f := (herm σ e v)⁻¹ • v + c • e with hf
  have hef : herm σ e f = 1 := by
    rw [hf]
    simp only [herm_add_right, herm_smul_right, he, mul_zero, add_zero,
      inv_mul_cancel₀ hev]
  have hff : herm σ f f = 0 := by rw [hf]; exact hc
  obtain ⟨z, hzz, hez, hfz⟩ := exists_norm_one_perp_pair hσ hn he hff hef
  obtain ⟨ν, hν⟩ := hσ.exists_norm (d := -(c + σ c)) (by
    rw [map_neg, map_add, hσ.invol, add_comm])
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hσ.invol, hef, map_one]
  have hze : herm σ z e = 0 := by rw [herm_conj σ hσ.invol, hez, map_zero]
  have hzf : herm σ z f = 0 := by rw [herm_conj σ hσ.invol, hfz, map_zero]
  have hae : herm σ (σ c • e + f + ν • z) e = 1 := by
    simp only [herm_add_left, herm_smul_left, he, hfe, hze, mul_zero, zero_mul, add_zero,
      zero_add]
  have haf : herm σ (σ c • e + f + ν • z) f = c := by
    simp only [herm_add_left, herm_smul_left, hef, hff, hzf, hσ.invol, mul_one, mul_zero,
      zero_mul, add_zero, zero_add]
  have haz : herm σ (σ c • e + f + ν • z) z = σ ν := by
    simp only [herm_add_left, herm_smul_left, hez, hfz, hzz, mul_one, mul_zero, zero_mul,
      add_zero, zero_add]
  have haa : herm σ (σ c • e + f + ν • z) (σ c • e + f + ν • z) = 0 := by
    simp only [herm_add_right, herm_smul_right, hae, haf, haz, mul_one]
    rw [mul_comm ν (σ ν), hν]
    ring
  have hveq : v = (herm σ e v) • f - (herm σ e v * c) • e := by
    rw [hf, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hev, one_smul]
    abel
  refine ⟨σ c • e + f + ν • z, haa, ?_, ?_⟩
  · rw [hveq, herm_sub_right, herm_smul_right, herm_smul_right, hae, haf]
    ring
  · rw [hae]
    exact one_ne_zero

private lemma exists_iso_of_herm_eq_zero_of_isotropic (hσ : IsUnitaryInvolution σ)
    {e v : Fin n → K} (he : herm σ e e = 0) (hvv : herm σ v v = 0)
    (hev : herm σ e v = 0) (hv0 : v ≠ 0) (hev' : ∀ c : K, e ≠ c • v) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨d, hd, hvd, hed⟩ := exists_iso_perp hσ hv0 hvv he
    (herm_eq_zero_comm σ hσ.invol hev) hev'
  have hde : herm σ d e ≠ 0 := fun h =>
    hed (by rw [herm_conj σ hσ.invol d e, h, map_zero])
  exact ⟨d, hd, herm_eq_zero_comm σ hσ.invol hvd, hde⟩

private lemma exists_iso_of_herm_eq_zero_of_anisotropic (hσ : IsUnitaryInvolution σ)
    {e v : Fin n → K} (he : herm σ e e = 0) (he0 : e ≠ 0)
    (hev : herm σ e v = 0) (hvv : herm σ v v ≠ 0) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hvv
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hve : herm σ v e = 0 := herm_eq_zero_comm σ hσ.invol hev
  have hce : herm σ (c • v) e = 0 := by rw [herm_smul_left, hve, mul_zero]
  obtain ⟨w, hcw, hww, hew⟩ := exists_partner_perp hσ hc he0 he hce
  have hvw : herm σ v w = 0 := by
    have h := hcw
    rw [herm_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hc0)
  refine ⟨w, hww, herm_eq_zero_comm σ hσ.invol hvw, ?_⟩
  rw [herm_conj σ hσ.invol, hew, map_one]
  exact one_ne_zero

theorem exists_isotropic_herm_eq_zero_herm_ne_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {e v : Fin n → K} (he : herm σ e e = 0) (he0 : e ≠ 0) (hv : ∀ c : K, v ≠ c • e) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv 0 (by simp)
  have hev' : ∀ c : K, e ≠ c • v := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact he0 (by simpa using hc)
    exact hv c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  by_cases hev : herm σ e v = 0
  · by_cases hvv : herm σ v v = 0
    · exact exists_iso_of_herm_eq_zero_of_isotropic hσ he hvv hev hv0 hev'
    · exact exists_iso_of_herm_eq_zero_of_anisotropic hσ he he0 hev hvv
  · exact exists_iso_of_herm_ne_zero hσ hn he hev

section Fix

open Matrix

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_fix_smul_eq (hσ : IsUnitaryInvolution σ) {a b b' : Fin n → K}
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hb' : herm σ b' b' = 0)
    (hab : herm σ a b ≠ 0) (hab' : herm σ a b' ≠ 0) :
    ∃ g : SUid σ n, g • a = a ∧ g • b = (herm σ a b / herm σ a b') • b' := by
  set b₁ := (herm σ a b)⁻¹ • b with hb₁
  set b₂ := (herm σ a b')⁻¹ • b' with hb₂
  have hab₁ : herm σ a b₁ = 1 := by rw [hb₁, herm_smul_right, inv_mul_cancel₀ hab]
  have hab₂ : herm σ a b₂ = 1 := by rw [hb₂, herm_smul_right, inv_mul_cancel₀ hab']
  have hb₁a : herm σ b₁ a = 1 := by rw [herm_conj σ hσ.invol, hab₁, map_one]
  have hb₂a : herm σ b₂ a = 1 := by rw [herm_conj σ hσ.invol, hab₂, map_one]
  have hb₁b₁ : herm σ b₁ b₁ = 0 := by rw [hb₁, herm_smul_left, herm_smul_right, hb]; ring
  have hb₂b₂ : herm σ b₂ b₂ = 0 := by rw [hb₂, herm_smul_left, herm_smul_right, hb']; ring
  set c := herm σ b₁ b₂ with hc
  have hb₂b₁ : herm σ b₂ b₁ = σ c := herm_conj σ hσ.invol b₁ b₂
  set y := b₂ - b₁ - c • a with hy
  have hay : herm σ a y = 0 := by rw [hy]; simp [hab₁, hab₂, ha]
  have hyb₁ : herm σ y b₁ = 0 := by rw [hy]; simp [hb₂b₁, hb₁b₁, hab₁]
  have hcy : c + σ c = -herm σ y y := by
    rw [hy]
    simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right, hb₂b₂, hb₁b₁,
      hb₂b₁, ← hc, hb₂a, hb₁a, hab₁, hab₂, ha]
    ring
  set E := eichler hσ.invol ha hay hcy with hE
  have hEb₁ : E • b₁ = b₂ := by
    rw [hE, eichler_smul, hab₁, hyb₁, one_smul, zero_smul, sub_zero, hy]
    abel
  refine ⟨E, eichler_smul_self hσ.invol ha hay hcy, ?_⟩
  have hb1 : b = herm σ a b • b₁ := by rw [hb₁, smul_smul, mul_inv_cancel₀ hab, one_smul]
  conv_lhs => rw [hb1]
  rw [smul_comm, hEb₁, hb₂, smul_smul, div_eq_mul_inv]

theorem exists_fix_herm_ne_zero (hσ : IsUnitaryInvolution σ) {a b : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm σ a a = 0) (hb : herm σ b b = 0) (hab : herm σ a b = 0)
    (hba : ∀ c : K, b ≠ c • a) : ∃ g : SUid σ n, g • a = a ∧ herm σ b (g • b) ≠ 0 := by
  obtain ⟨d, hd, had, hbd⟩ := exists_iso_perp hσ ha0 ha hb hab hba
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hda : herm σ d a = 0 := herm_eq_zero_comm σ hσ.invol had
  refine ⟨tv hσ.invol hd hτ, ?_, ?_⟩
  · rw [tv_smul, hda, mul_zero, zero_smul, add_zero]
  · rw [tv_smul, herm_add_right, herm_smul_right, hb, zero_add, herm_conj σ hσ.invol b d]
    exact mul_ne_zero (mul_ne_zero hτ0 ((map_ne_zero σ).mpr hbd)) hbd

end Fix

end CFSGOutside.HallPaige.Unitary
