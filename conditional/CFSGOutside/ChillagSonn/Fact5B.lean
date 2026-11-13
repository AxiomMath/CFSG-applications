import CFSGOutside.ChillagSonn.Fact5A

/-!
# Fact 5 of Chillag–Sonn, part B: `PGL*(2, p²)` and the arithmetic of `𝔽_{p²}`

The elements `(g, τ)` of `PGL*(2, F)` have `τ = 1` exactly when `g ∈ PSL(2, F)`. For `|F| = p²`, `p` odd, the
nontrivial field automorphism is `x ↦ xᵖ`; if `g σ(g) = s λ` and `s g = g σ(s)` with `det s = 1`, `λ` scalar, then
`det g` is a square in `F`.
-/

noncomputable section

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GorensteinWalter Matrix SemidirectProduct
open scoped MatrixGroups

variable {F : Type} [Field F]

/-- Field automorphisms preserve the image of `PSL(2, F)`. -/
theorem fieldAut_mem_pslT_of_mem (τ : F ≃+* F) {y : PGL2 F} (hy : y ∈ pslT F) :
    pgl2FieldAut F τ y ∈ pslT F := by
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨(SpecialLinearGroup.map (τ : F →+* F) s : PSL2 F), ?_⟩
  change ProjGenLinGroup.mk _ = ProjGenLinGroup.mk (GeneralLinearGroup.map (τ : F →+* F) (SpecialLinearGroup.toGL s))
  congr 1
  ext; rfl

/-- A field automorphism maps `g` into `PSL(2, F)` iff `g ∈ PSL(2, F)`. -/
theorem fieldAut_mem_pslT_iff (τ : F ≃+* F) (y : PGL2 F) : pgl2FieldAut F τ y ∈ pslT F ↔ y ∈ pslT F :=
  ⟨fun h => by simpa [← MulAut.mul_apply, ← map_mul] using fieldAut_mem_pslT_of_mem τ⁻¹ h,
    fieldAut_mem_pslT_of_mem τ⟩

/-- In `PGL*(2, F)`, the field automorphism is trivial exactly when the `PGL`-part is in `PSL(2, F)`. -/
theorem right_eq_one_iff_of_mem_pglStar [Finite F] (hK : ringChar F ≠ 2) (h2 : Nat.card (F ≃+* F) = 2)
    {x : PGammaL2 F} (hx : x ∈ PGLStar F) : x.right = 1 ↔ x.left ∈ pslT F := by
  have hT := index_pslT hK
  have huniq := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp h2
  have hsq : ∀ a : F ≃+* F, a * a = 1 := fun a => by
    have := pow_card_eq_one' (x := a); rwa [h2, sq] at this
  have hmul : ∀ a b : F ≃+* F, a * b = 1 ↔ (a = 1 ↔ b = 1) := fun a b => by
    rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_left (hsq b)]
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · simp [ha, hb]
    · simp [ha, hb, Ne.symm hb]
    · simp [ha, hb]
    · exact iff_of_true (huniq.unique ha hb) (iff_of_false ha hb)
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨h1, h⟩ | ⟨h1, h⟩
    · exact iff_of_true h1 h
    · exact iff_of_false h1 h
  | one => exact iff_of_true rfl (one_mem _)
  | mul x y _ _ hx hy =>
    rw [mul_right, mul_left, Subgroup.mul_mem_iff_of_index_two hT, fieldAut_mem_pslT_iff, hmul]
    exact iff_congr hx hy
  | inv x _ hx => rw [inv_right, inv_left, fieldAut_mem_pslT_iff, inv_mem_iff, inv_eq_one]; exact hx

/-- Every field automorphism `τ ≠ 1` occurs in `PGL*(2, F)`. -/
theorem exists_mem_pglStar_right [Finite F] (hK : ringChar F ≠ 2) {τ : F ≃+* F} (hτ : τ ≠ 1) :
    ∃ x ∈ PGLStar F, x.right = τ := by
  have hT := index_pslT hK
  obtain ⟨y, hy⟩ : ∃ y, y ∉ pslT F := by
    by_contra h
    push Not at h
    rw [show pslT F = ⊤ from eq_top_iff.mpr fun y _ => h y, Subgroup.index_top] at hT
    omega
  exact ⟨⟨y, τ⟩, Subgroup.subset_closure (Or.inr ⟨hτ, hy⟩), rfl⟩

/-- An element of `PGL(2, F)` outside `PSL(2, F)` has non-square determinant. -/
theorem not_isSquare_det [Finite F] (hK : ringChar F ≠ 2) (g : GL (Fin 2) F)
    (hg : ProjGenLinGroup.mk g ∉ pslT F) : ¬ IsSquare (GeneralLinearGroup.det g) := by
  rintro ⟨w, hw⟩
  apply hg
  refine (Subgroup.mem_map_iff_mem (f := (inl : PGL2 F →* PGammaL2 F)) inl_injective).mp
    (LinearTwo.Phi_ker_le F hK (inl (ProjGenLinGroup.mk g)) (Prod.ext ?_ rfl))
  change LinearTwo.detQ F (ProjGenLinGroup.mk g) = 1
  rw [LinearTwo.detQ_mk, QuotientGroup.eq_one_iff, LinearTwo.mem_sqSub]
  exact ⟨w, by rw [hw, sq]⟩

/-- For `|F| = p²`, the nontrivial field automorphism is `x ↦ xᵖ`. -/
theorem ringEquiv_apply_eq_pow [Finite F] {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2) {σ : F ≃+* F}
    (hσ : σ ≠ 1) (y : F) : σ y = y ^ p := by
  have := Fact.mk hp
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have huniq := (Nat.card_eq_two_iff' (1 : F ≃+* F)).mp (card_ringEquiv hF)
  have hinj := (frobenius F p).injective
  let fr : F ≃+* F := RingEquiv.ofBijective (frobenius F p) ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hfr : fr ≠ 1 := by
    intro h
    have h1 : ∀ x : Fˣ, x ^ (p - 1) = 1 := fun x => by
      have hx : (x : F) ^ p = x := by
        have := DFunLike.congr_fun h (x : F)
        simp only [fr] at this
        exact this
      have : x ^ (p - 1) * x = 1 * x := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul]; exact Units.ext (by simpa using hx)
      exact mul_right_cancel this
    have h2 := (FiniteField.forall_pow_eq_one_iff F (p - 1)).mp h1
    rw [← Nat.card_eq_fintype_card, hF] at h2
    have h3 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) h2
    have h4 : p < p ^ 2 := by nlinarith [hp.two_le]
    have h5 := hp.two_le
    generalize p ^ 2 = q at h3 h4
    omega
  rw [huniq.unique hσ hfr]
  rfl

/-- An involutive field automorphism acts involutively on `GL(2, F)`. -/
theorem map_map_of_mul_self {σ : F ≃+* F} (hσ : σ * σ = 1) (x : GL (Fin 2) F) :
    GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.map (σ : F →+* F) x) = x := by
  ext i j
  simpa using DFunLike.congr_fun hσ (x i j)

/-- If `g σ(g) = s λ` and `g σ(s) = s g` with `det s = 1` and `λ` scalar, then `det g` is a square. -/
theorem isSquare_det_of_semilinear [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {σ : F ≃+* F} (hσ : σ ≠ 1) (g S : GL (Fin 2) F) (hS : GeneralLinearGroup.det S = 1) (u : Fˣ)
    (E1 : g * GeneralLinearGroup.map (σ : F →+* F) S = S * g)
    (E2 : g * GeneralLinearGroup.map (σ : F →+* F) g = S * GeneralLinearGroup.scalar (Fin 2) u) :
    IsSquare (GeneralLinearGroup.det g) := by
  have := Fintype.ofFinite F
  have := Fact.mk hp
  have hF' : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hF'
  have hK : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hpow := ringEquiv_apply_eq_pow hp hF hσ
  have hσσ' : ∀ y : F, σ (σ y) = y := fun y => by
    rw [hpow, hpow, ← pow_mul, ← sq, ← hF', FiniteField.pow_card]
  have hupow : ∀ x : Fˣ, Units.map ((σ : F →+* F) : F →* F) x = x ^ p := fun x => Units.ext (by simp [hpow])
  set σ' := GeneralLinearGroup.map (n := Fin 2) (σ : F →+* F)
  have hσσ : ∀ x, σ' (σ' x) = x := fun x => by
    ext i j; simp [σ', hσσ']
  have hsc : σ' (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : F →+* F) : F →* F) u) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σ', GeneralLinearGroup.coe_scalar]
  have E2σ := congrArg σ' E2
  rw [map_mul, map_mul, hσσ, hsc] at E2σ
  have key : S * g * GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : F →+* F) : F →* F) u) =
      S * g * GeneralLinearGroup.scalar (Fin 2) u := by
    calc _ = g * (σ' S * GeneralLinearGroup.scalar (Fin 2) (Units.map ((σ : F →+* F) : F →* F) u)) := by
          rw [← E1, mul_assoc]
      _ = g * σ' g * g := by rw [← E2σ, mul_assoc]
      _ = S * g * GeneralLinearGroup.scalar (Fin 2) u := by
          rw [E2, mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc]
  have hu : u ^ p = u := by
    have h := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) (mul_left_cancel key)
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h
    rw [← hupow]; exact Units.ext h
  have hdet := congrArg GeneralLinearGroup.det E2
  rw [map_mul, map_mul, GeneralLinearGroup.map_det, GeneralLinearGroup.det_scalar, hS, one_mul,
    Fintype.card_fin, hupow, ← pow_succ'] at hdet
  obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp2
  have hcard : Fintype.card F / 2 = (2 * k + 1 + 1) * k := by
    rw [hF', show (2 * k + 1) ^ 2 = 2 * ((2 * k + 1 + 1) * k) + 1 by ring, Nat.mul_add_div two_pos]
    simp
  have hu1 : u ^ (2 * k) = 1 := by
    rw [pow_succ] at hu
    exact mul_eq_right.mp hu
  rw [FiniteField.unit_isSquare_iff hK, hcard, pow_mul, hdet, ← pow_mul, hu1]

end CFSGOutside.ChillagSonn
