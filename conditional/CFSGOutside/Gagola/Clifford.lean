import CFSGOutside.Gagola.Chars

/-!
# Clifford theory for a normal subgroup, at the level of characters

For `N ⊴ A` and `σ ∈ Irr N`: the conjugates `x • σ`, the inertia group, Clifford's theorem (the
constituents of `ζ_N` form one `A`-orbit with a common multiplicity) and the Clifford correspondence
(`ζ` is induced from a character of the inertia group lying over `σ` with the same multiplicity).
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

variable {A : Type*} [Group A] [Fintype A] (N : Subgroup A) [hN : N.Normal]

theorem conj_inv_mem (x : A) (n : N) : x⁻¹ * (n : A) * x ∈ N := by
  simpa using hN.conj_mem n n.2 x⁻¹

/-- The conjugate `(x • σ)(n) = σ(x⁻¹ n x)`. -/
def conjN (x : A) (σ : N → ℂ) : N → ℂ := fun n => σ ⟨x⁻¹ * n * x, conj_inv_mem N x n⟩

variable {N}

@[simp] theorem conjN_apply (x : A) (σ : N → ℂ) (n : N) :
    conjN N x σ n = σ ⟨x⁻¹ * n * x, conj_inv_mem N x n⟩ := rfl

theorem conjN_one (σ : N → ℂ) : conjN N 1 σ = σ := by
  funext n; simp

theorem conjN_mul (x y : A) (σ : N → ℂ) : conjN N (x * y) σ = conjN N x (conjN N y σ) := by
  funext n
  simp only [conjN_apply]
  congr 2
  group

/-- `conjN x` is pulling back along the automorphism `n ↦ x⁻¹ n x`. -/
theorem conjN_eq_pull (x : A) (σ : N → ℂ) :
    conjN N x σ = pull (MulAut.conjNormal x⁻¹).toMonoidHom σ := by
  funext n
  simp only [conjN_apply, pull_apply]
  congr 1
  ext
  simp [MulAut.conjNormal_apply]

theorem conjN_mem_irr (x : A) {σ : N → ℂ} (hσ : σ ∈ Irr N) : conjN N x σ ∈ Irr N := by
  rw [conjN_eq_pull]
  exact irr_pull_mulEquiv _ hσ

theorem ip_conjN (x : A) (σ τ : N → ℂ) : ip (conjN N x σ) (conjN N x τ) = ip σ τ := by
  rw [conjN_eq_pull, conjN_eq_pull]
  exact ip_pull_mulEquiv _ σ τ

theorem conjN_of_mem {σ : N → ℂ} (hσ : IsClassFn σ) {x : A} (hx : x ∈ N) : conjN N x σ = σ := by
  funext n
  simp only [conjN_apply]
  have := hσ.conj_eq n ⟨x, hx⟩
  convert this using 2

theorem conjN_res {ζ : A → ℂ} (hζ : IsClassFn ζ) (x : A) :
    conjN N x (pull N.subtype ζ) = pull N.subtype ζ := by
  funext n
  simp only [conjN_apply, pull_apply, Subgroup.coe_subtype]
  exact hζ.conj_eq n x

theorem ip_res_conjN {ζ : A → ℂ} (hζ : IsClassFn ζ) (x : A) (σ : N → ℂ) :
    ip (pull N.subtype ζ) (conjN N x σ) = ip (pull N.subtype ζ) σ := by
  conv_lhs => rw [← conjN_res hζ x]
  exact ip_conjN x _ σ

theorem mult_res_conjN {ζ : A → ℂ} (hζ : IsClassFn ζ) (x : A) (σ : N → ℂ) :
    mult (pull N.subtype ζ) (conjN N x σ) = mult (pull N.subtype ζ) σ := by
  simp only [mult, ip_res_conjN hζ x σ]

/-- The inertia group of `σ`. -/
def inertia (σ : N → ℂ) : Subgroup A where
  carrier := {x | conjN N x σ = σ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    rw [conjN_mul, hy, hx]
  one_mem' := conjN_one σ
  inv_mem' {x} hx := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx, ← conjN_mul, inv_mul_cancel, conjN_one]

theorem mem_inertia {σ : N → ℂ} {x : A} : x ∈ inertia σ ↔ conjN N x σ = σ := Iff.rfl

theorem le_inertia {σ : N → ℂ} (hσ : IsClassFn σ) : N ≤ inertia σ := fun _ hx => conjN_of_mem hσ hx

/-- The restriction of an induced function to the normal subgroup. -/
theorem res_ind (σ : N → ℂ) :
    pull N.subtype (ind N σ) = (Nat.card N : ℂ)⁻¹ • ∑ x : A, conjN N x σ := by
  funext n
  simp only [pull_apply, Subgroup.coe_subtype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [ind_apply_of_normal]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv A) _ _ (fun x => ?_)
  simp only [Equiv.inv_apply, conjN_apply, inv_inv]

/-- The pairing of the orbit sum with an irreducible character counts conjugates. -/
theorem ip_sum_conjN {σ τ : N → ℂ} (hσ : σ ∈ Irr N) (hτ : τ ∈ Irr N) :
    ip (∑ x : A, conjN N x σ) τ = ((Finset.univ.filter fun x : A => conjN N x σ = τ).card : ℂ) := by
  rw [ip_sum_left]
  simp_rw [ip_irr (conjN_mem_irr _ hσ) hτ]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]

/-- The orbit of `σ`. -/
def orbitF (σ : N → ℂ) : Finset (N → ℂ) := Finset.univ.image fun x : A => conjN N x σ

theorem orbitF_subset_irr {σ : N → ℂ} (hσ : σ ∈ Irr N) : ∀ τ ∈ orbitF (A := A) σ, τ ∈ Irr N := by
  intro τ hτ
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hτ
  exact conjN_mem_irr x hσ

/-- The fibres of `x ↦ x • σ` are the cosets of the inertia group. -/
theorem card_filter_conjN {σ : N → ℂ} (x₀ : A) :
    (Finset.univ.filter fun x : A => conjN N x σ = conjN N x₀ σ).card = Nat.card (inertia σ) := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
  refine Fintype.card_congr ⟨fun x => ⟨x₀⁻¹ * x, ?_⟩, fun y => ⟨x₀ * y, ?_⟩, ?_, ?_⟩
  · have hx := (Finset.mem_filter.mp x.2).2
    show conjN N (x₀⁻¹ * x) σ = σ
    rw [conjN_mul, hx, ← conjN_mul, inv_mul_cancel, conjN_one]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conjN_mul, (mem_inertia.mp y.2)]
  · intro x; ext; simp
  · intro y; ext; simp

theorem card_orbitF_mul (σ : N → ℂ) :
    (orbitF (A := A) σ).card * Nat.card (inertia σ) = Nat.card A := by
  rw [Nat.card_eq_fintype_card (α := A), ← Finset.card_univ,
    Finset.card_eq_sum_card_image (fun x : A => conjN N x σ) Finset.univ, orbitF]
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hτ
  exact (card_filter_conjN x₀).symm

theorem index_inertia (σ : N → ℂ) : (inertia (N := N) σ).index = (orbitF (A := A) σ).card := by
  have h := card_orbitF_mul (A := A) σ
  have h2 := (inertia (N := N) σ).card_mul_index
  have hpos : 0 < Nat.card (inertia (N := N) σ) := Nat.card_pos
  rw [mul_comm] at h2
  have : (inertia (N := N) σ).index * Nat.card (inertia (N := N) σ) =
      (orbitF (A := A) σ).card * Nat.card (inertia (N := N) σ) := by rw [h, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

variable {ζ : A → ℂ} {σ : N → ℂ}

/-- An irreducible `ζ` lies below `σ^A` whenever `σ` is a constituent of `ζ_N`. -/
theorem charLE_ind (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0) :
    CharLE ζ (ind N σ) := by
  have hind : IsNatComb (ind N σ) := (irr_isNatComb hσ).ind
  refine charLE_of_mult_pos hind hζ ?_
  have h1 := hind.mult_eq hζ
  rw [ip_ind N σ (irr_isClassFn hζ), ip_comm, ← ((irr_isNatComb hζ).pull N.subtype).mult_eq hσ] at h1
  have : mult (ind N σ) ζ = mult (pull N.subtype ζ) σ := by exact_mod_cast h1
  omega

/-- **Clifford's theorem**: every constituent of `ζ_N` is a conjugate of `σ`. -/
theorem clifford_conj (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0)
    {τ : N → ℂ} (hτ : τ ∈ Irr N) (hτ' : mult (pull N.subtype ζ) τ ≠ 0) :
    ∃ x : A, conjN N x σ = τ := by
  by_contra hno
  push Not at hno
  have hle := (charLE_ind hζ hσ h).pull N.subtype
  have hm := hle.mult_le ((irr_isNatComb hζ).pull N.subtype) hτ
  have hz : mult (pull N.subtype (ind N σ)) τ = 0 := by
    have h1 := ((irr_isNatComb hσ).ind.pull N.subtype).mult_eq hτ
    have h2 : ip (pull N.subtype (ind N σ)) τ = 0 := by
      rw [res_ind, ip_smul_left, ip_sum_conjN hσ hτ, Finset.filter_false_of_mem (fun x _ => hno x),
        Finset.card_empty]; simp
    rw [h2] at h1; exact_mod_cast h1
  omega

/-- **Clifford's theorem**: `ζ_N = b ∑_{τ ∈ orbit} τ`. -/
theorem clifford_res (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0) :
    pull N.subtype ζ = (mult (pull N.subtype ζ) σ : ℂ) • ∑ τ ∈ orbitF (A := A) σ, τ := by
  have hres := (irr_isNatComb hζ).pull N.subtype
  conv_lhs => rw [hres.eq_sum]
  rw [Finset.smul_sum]
  rw [← Finset.sum_subset (fun τ hτ => mem_irrFinset.mpr (orbitF_subset_irr hσ τ hτ))]
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hτ
    rw [mult_res_conjN (irr_isClassFn hζ)]
  · intro τ hτ hτo
    have : mult (pull N.subtype ζ) τ = 0 := by
      by_contra hne
      obtain ⟨x, rfl⟩ := clifford_conj hζ hσ h (mem_irrFinset.mp hτ) hne
      exact hτo (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    rw [this]; simp

theorem mult_res_eq (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0)
    {τ : N → ℂ} (hτ : τ ∈ orbitF (A := A) σ) :
    mult (pull N.subtype ζ) τ = mult (pull N.subtype ζ) σ := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hτ
  exact mult_res_conjN (irr_isClassFn hζ) x σ

/-- The squared norm of `ζ_N` is `b² · |orbit|`. -/
theorem ip_res_self (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0) :
    ip (pull N.subtype ζ) (pull N.subtype ζ) =
      ((mult (pull N.subtype ζ) σ ^ 2 * (orbitF (A := A) σ).card : ℕ) : ℂ) := by
  have hres := (irr_isNatComb hζ).pull N.subtype
  rw [ip_natComb_self hres]
  rw [← Finset.sum_subset (fun τ hτ => mem_irrFinset.mpr (orbitF_subset_irr hσ τ hτ))]
  · rw [Finset.sum_congr rfl fun τ hτ => by rw [mult_res_eq hζ hσ h hτ], Finset.sum_const,
      nsmul_eq_mul]
    push_cast; ring
  · intro τ hτ hτo
    have : mult (pull N.subtype ζ) τ = 0 := by
      by_contra hne
      obtain ⟨x, rfl⟩ := clifford_conj hζ hσ h (mem_irrFinset.mp hτ) hne
      exact hτo (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    rw [this]; simp

section Correspondence

/-- The inclusion of `N` in the inertia group of `σ`. -/
abbrev inclI (hσ : σ ∈ Irr N) : N →* inertia (N := N) σ :=
  Subgroup.inclusion (le_inertia (irr_isClassFn hσ))

theorem inclI_injective (hσ : σ ∈ Irr N) : Function.Injective (inclI hσ) :=
  Subgroup.inclusion_injective _

theorem pull_inclI_res (hσ : σ ∈ Irr N) (ζ : A → ℂ) :
    pull (inclI hσ) (pull (inertia (N := N) σ).subtype ζ) = pull N.subtype ζ := rfl

/-- Inducing `σ` to its inertia group and restricting back multiplies by the index. -/
theorem pull_indHom_inclI (hσ : σ ∈ Irr N) :
    pull (inclI hσ) (indHom (inclI hσ) σ) =
      ((Nat.card (inertia (N := N) σ) : ℂ) * (Nat.card N : ℂ)⁻¹) • σ := by
  funext n
  simp only [pull_apply, indHom, Pi.smul_apply, smul_eq_mul]
  have key : ∀ t : inertia (N := N) σ,
      Function.extend (inclI hσ) σ 0 (t * inclI hσ n * t⁻¹) = σ n := by
    intro t
    have hmem : (t : A) * n * (t : A)⁻¹ ∈ N := hN.conj_mem n n.2 t
    have he : t * inclI hσ n * t⁻¹ = inclI hσ ⟨(t : A) * n * (t : A)⁻¹, hmem⟩ := by
      ext; simp
    rw [he, (inclI_injective hσ).extend_apply]
    have ht : conjN N (t : A)⁻¹ σ = σ := mem_inertia.mp ((inertia σ).inv_mem t.2)
    have := congrFun ht n
    simp only [conjN_apply, inv_inv] at this
    rw [← this]
  rw [Finset.sum_congr rfl fun t _ => key t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  ring

/-- Clifford's theorem inside the inertia group: a character of `I(σ)` over `σ` restricts to a
multiple of `σ`. -/
theorem res_inertia_eq (hσ : σ ∈ Irr N) {ψ : inertia (N := N) σ → ℂ} (hψ : ψ ∈ Irr _)
    (h : mult (pull (inclI hσ) ψ) σ ≠ 0) :
    pull (inclI hσ) ψ = (mult (pull (inclI hσ) ψ) σ : ℂ) • σ := by
  have hres := (irr_isNatComb hψ).pull (inclI hσ)
  have hind : IsNatComb (indHom (inclI hσ) σ) := (irr_isNatComb hσ).indHom (inclI_injective hσ)
  have hle : CharLE ψ (indHom (inclI hσ) σ) := by
    refine charLE_of_mult_pos hind hψ ?_
    have h1 := hind.mult_eq hψ
    rw [ip_indHom (inclI_injective hσ) σ (irr_isClassFn hψ), ip_comm, ← hres.mult_eq hσ] at h1
    have : mult (indHom (inclI hσ) σ) ψ = mult (pull (inclI hσ) ψ) σ := by exact_mod_cast h1
    omega
  have hle' := hle.pull (inclI hσ)
  rw [pull_indHom_inclI] at hle'
  conv_lhs => rw [hres.eq_sum]
  rw [Finset.sum_eq_single σ]
  · intro τ hτ hne
    have hm := hle'.mult_le hres (mem_irrFinset.mp hτ)
    have hz : mult (((Nat.card (inertia (N := N) σ) : ℂ) * (Nat.card N : ℂ)⁻¹) • σ) τ = 0 := by
      unfold mult
      rw [ip_smul_left, ip_irr hσ (mem_irrFinset.mp hτ), if_neg (Ne.symm hne)]
      simp
    rw [show mult (pull (inclI hσ) ψ) τ = 0 by omega]
    simp
  · intro hσ'; exact absurd (mem_irrFinset.mpr hσ) hσ'

/-- **Clifford correspondence**: `ζ` is induced from a character `φ` of the inertia group with
`φ_N = b σ`, where `b` is the multiplicity of `σ` in `ζ_N`. -/
theorem clifford_corr (hζ : ζ ∈ Irr A) (hσ : σ ∈ Irr N) (h : mult (pull N.subtype ζ) σ ≠ 0) :
    ∃ φ ∈ Irr (inertia (N := N) σ),
      pull (inclI hσ) φ = (mult (pull N.subtype ζ) σ : ℂ) • σ ∧ ind (inertia (N := N) σ) φ = ζ := by
  set T := inertia (N := N) σ
  have hresT := (irr_isNatComb hζ).pull T.subtype
  -- the multiplicity of `σ` in `ζ_N`, computed through `ζ_T`
  have hsum : mult (pull N.subtype ζ) σ =
      ∑ ψ ∈ irrFinset T, mult (pull T.subtype ζ) ψ * mult (pull (inclI hσ) ψ) σ := by
    rw [← pull_inclI_res hσ ζ]
    conv_lhs => rw [hresT.eq_sum, pull_sum]
    rw [mult_sum _ (fun ψ hψ => ?_) hσ]
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      rw [pull_smul, mult_nsmul ((irr_isNatComb (mem_irrFinset.mp hψ)).pull _) _ hσ]
    · rw [pull_smul]
      exact ((irr_isNatComb (mem_irrFinset.mp hψ)).pull _).nsmul _
  obtain ⟨ψ₀, hψ₀, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum ▸ h)
  have hψ₀' := mem_irrFinset.mp hψ₀
  have hm₀ : mult (pull T.subtype ζ) ψ₀ ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have he₀ : mult (pull (inclI hσ) ψ₀) σ ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  set e := mult (pull (inclI hσ) ψ₀) σ with he_def
  have hψ₀N := res_inertia_eq hσ hψ₀' he₀
  rw [← he_def] at hψ₀N
  -- the restriction of `ψ₀^A` to `N`
  have hind : IsNatComb (ind T ψ₀) := (irr_isNatComb hψ₀').ind
  have hresind : pull N.subtype (ind T ψ₀) =
      ((e : ℂ) * (Nat.card T : ℂ)⁻¹) • ∑ x : A, conjN N x σ := by
    funext n
    simp only [pull_apply, Subgroup.coe_subtype, ind, indHom, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul]
    have key : ∀ x : A, Function.extend (Subtype.val : T → A) ψ₀ 0 (x * (n : A) * x⁻¹) =
        (e : ℂ) * conjN N x⁻¹ σ n := by
      intro x
      have hmem : x * (n : A) * x⁻¹ ∈ N := hN.conj_mem n n.2 x
      have he : x * (n : A) * x⁻¹ = ((inclI hσ ⟨x * n * x⁻¹, hmem⟩ : T) : A) := rfl
      rw [he, Subtype.val_injective.extend_apply]
      have := congrFun hψ₀N ⟨x * n * x⁻¹, hmem⟩
      simp only [pull_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      simp only [conjN_apply, inv_inv]
    rw [Finset.sum_congr rfl fun x _ => key x, ← Finset.mul_sum]
    have : ∑ x : A, conjN N x⁻¹ σ n = ∑ x : A, conjN N x σ n :=
      Fintype.sum_equiv (Equiv.inv A) _ _ (fun x => rfl)
    rw [this]; ring
  have hmultind : mult (pull N.subtype (ind T ψ₀)) σ = e := by
    have h1 := (hind.pull N.subtype).mult_eq hσ
    have h2 : ip (pull N.subtype (ind T ψ₀)) σ = e := by
      rw [hresind, ip_smul_left, ip_sum_conjN hσ hσ]
      have hc := card_filter_conjN (N := N) (σ := σ) 1
      rw [conjN_one] at hc
      rw [hc]
      have : (Nat.card T : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
      field_simp
      rfl
    rw [h2] at h1; exact_mod_cast h1
  -- every constituent of `ψ₀^A` has `σ`-multiplicity at least `e`
  have hlow : ∀ χ ∈ Irr A, mult (ind T ψ₀) χ ≠ 0 → e ≤ mult (pull N.subtype χ) σ := by
    intro χ hχ hχ0
    have hresχ := (irr_isNatComb hχ).pull T.subtype
    have h1 := hind.mult_eq hχ
    rw [ip_ind T ψ₀ (irr_isClassFn hχ), ip_comm, ← hresχ.mult_eq hψ₀'] at h1
    have h2 : mult (ind T ψ₀) χ = mult (pull T.subtype χ) ψ₀ := by exact_mod_cast h1
    have hle := (charLE_of_mult_pos hresχ hψ₀' (by omega)).pull (inclI hσ)
    exact hle.mult_le ((irr_isNatComb hψ₀').pull _) hσ
  -- `ζ` is a constituent of `ψ₀^A`
  have hζin : mult (ind T ψ₀) ζ ≠ 0 := by
    have h1 := hind.mult_eq hζ
    rw [ip_ind T ψ₀ (irr_isClassFn hζ), ip_comm, ← hresT.mult_eq hψ₀'] at h1
    have h2 : mult (ind T ψ₀) ζ = mult (pull T.subtype ζ) ψ₀ := by exact_mod_cast h1
    omega
  -- counting
  have hcount : e = ∑ χ ∈ irrFinset A, mult (ind T ψ₀) χ * mult (pull N.subtype χ) σ := by
    rw [← hmultind]
    conv_lhs => rw [hind.eq_sum, pull_sum]
    rw [mult_sum _ (fun χ hχ => ?_) hσ]
    · refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [pull_smul, mult_nsmul ((irr_isNatComb (mem_irrFinset.mp hχ)).pull _) _ hσ]
    · rw [pull_smul]
      exact ((irr_isNatComb (mem_irrFinset.mp hχ)).pull _).nsmul _
  have hge : ∀ χ ∈ irrFinset A, mult (ind T ψ₀) χ * e ≤
      mult (ind T ψ₀) χ * mult (pull N.subtype χ) σ := by
    intro χ hχ
    by_cases h0 : mult (ind T ψ₀) χ = 0
    · rw [h0]; simp
    · exact Nat.mul_le_mul_left _ (hlow χ (mem_irrFinset.mp hχ) h0)
  have htot : (∑ χ ∈ irrFinset A, mult (ind T ψ₀) χ) * e ≤ e := by
    rw [Finset.sum_mul]
    calc _ ≤ _ := Finset.sum_le_sum hge
      _ = e := hcount.symm
  have hepos : 0 < e := Nat.pos_of_ne_zero he₀
  have hsum1 : ∑ χ ∈ irrFinset A, mult (ind T ψ₀) χ ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 * e ≤ (∑ χ ∈ irrFinset A, mult (ind T ψ₀) χ) * e := Nat.mul_le_mul_right _ hc
    omega
  have hζmem := mem_irrFinset.mpr hζ
  have hsplit := Finset.add_sum_erase (irrFinset A) (fun χ => mult (ind T ψ₀) χ) hζmem
  have hζ1 : mult (ind T ψ₀) ζ = 1 := by
    have : mult (ind T ψ₀) ζ ≤ 1 := by
      have := Finset.single_le_sum (f := fun χ => mult (ind T ψ₀) χ) (fun _ _ => Nat.zero_le _) hζmem
      omega
    omega
  have hrest : ∀ χ ∈ (irrFinset A).erase ζ, mult (ind T ψ₀) χ = 0 := by
    intro χ hχ
    have : ∑ χ ∈ (irrFinset A).erase ζ, mult (ind T ψ₀) χ = 0 := by
      omega
    exact Finset.sum_eq_zero_iff.mp this χ hχ
  have hindζ : ind T ψ₀ = ζ := by
    rw [hind.eq_sum, ← Finset.add_sum_erase _ _ hζmem, hζ1,
      Finset.sum_eq_zero fun χ hχ => by rw [hrest χ hχ]; simp]
    simp
  refine ⟨ψ₀, hψ₀', ?_, hindζ⟩
  rw [hψ₀N]
  congr 2
  rw [← hindζ, hmultind]

end Correspondence

end

end CFSGOutside.Gagola
