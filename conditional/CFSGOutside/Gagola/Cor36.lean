import CFSGOutside.Gagola.Cor36Lemmas

/-!
# Gagola, Corollary 3.6

Let `(H, Z, χ)` be a fully ramified triple, `Z ≤ K ⊴ H` with `H/K` a `p`-group and `K/Z` without
nontrivial `p`-group quotients (`K = O^p(H) Z`), and suppose a Sylow `p`-subgroup of `K/Z` is abelian.
Then `χ_K` has a single irreducible constituent `τ`, so that `(H, K, χ)` and `(K, Z, τ)` are fully
ramified triples.

The proof follows Gagola, with two changes. We work with `Z` not necessarily central (no appeal to his
Theorem 1.1), and the non-fusion statement of his Theorem 3.5 comes from `nonfusion`, whose
hypothesis — restriction from `K` onto the span of `Irr (D | θ)`, `D = R ∩ K` — is proved with the
mod-`p` spanning lemma `span_eq_top_of_modp`. The inequality `t ≤ s` between the numbers of
constituents of `χ_K` and `χ_D` (his Lemma 2.3(b)) is proved by a fixed-point count, using that the
multiplicities `a_τ = ⟨τ_D, σ⟩` and `b_σ = ⟨τ_D, σ⟩` satisfy `(∑ a_τ)(∑ b_σ) = |K : D|`.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

section Setup

variable {H : Type} [Group H] [Fintype H] (K R : Subgroup H)

/-- `D = R ∩ K`, as a normal subgroup of `R`. -/
abbrev DD : Subgroup R := K.subgroupOf R

/-- The inclusion `D → K`. -/
def ιDK : DD K R →* K where
  toFun d := ⟨((d : R) : H), Subgroup.mem_subgroupOf.mp d.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion `D → H`. -/
def ιDH : DD K R →* H := R.subtype.comp (DD K R).subtype

@[simp] theorem ιDK_apply (d : DD K R) : ((ιDK K R d : K) : H) = ((d : R) : H) := rfl
@[simp] theorem ιDH_apply (d : DD K R) : ιDH K R d = ((d : R) : H) := rfl

theorem ιDK_injective : Function.Injective (ιDK K R) := by
  intro a b h
  have : ((a : R) : H) = ((b : R) : H) := congrArg (fun x : K => (x : H)) h
  exact Subtype.ext (Subtype.ext this)

theorem ιDH_injective : Function.Injective (ιDH K R) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

variable {K R} {Z : Subgroup H}

/-- The inclusion `Z → D`. -/
def sD (hZR : Z ≤ R) (hZK : Z ≤ K) : Z →* DD K R where
  toFun z := ⟨⟨z, hZR z.2⟩, Subgroup.mem_subgroupOf.mpr (hZK z.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem sD_apply (hZR : Z ≤ R) (hZK : Z ≤ K) (z : Z) :
    (((sD hZR hZK z : DD K R) : R) : H) = z := rfl

/-- `Z` inside `D`. -/
abbrev ZD (K R Z : Subgroup H) : Subgroup (DD K R) := Z.comap (ιDH K R)

/-- `θ` transported to `Z` inside `D`. -/
def θD (θ : Z → ℂ) : ZD K R Z → ℂ := fun w => θ ⟨ιDH K R w, w.2⟩

/-- `Z` inside `D` is isomorphic to `Z`. -/
def eZD (hZR : Z ≤ R) (hZK : Z ≤ K) : ZD K R Z ≃* Z where
  toFun w := ⟨ιDH K R w, w.2⟩
  invFun z := ⟨sD hZR hZK z, z.2⟩
  left_inv w := by ext; rfl
  right_inv z := by ext; rfl
  map_mul' _ _ := rfl

theorem θD_eq (θ : Z → ℂ) (hZR : Z ≤ R) (hZK : Z ≤ K) :
    θD (K := K) (R := R) θ = pull (eZD hZR hZK).toMonoidHom θ := rfl

end Setup

section Main

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [hZ : Z.Normal] {χ : H → ℂ} {θ : Z → ℂ}
  {e : ℕ}

theorem e_ne_zero (he : e ^ 2 = Z.index) : e ≠ 0 := by
  rintro rfl
  exact Z.index_ne_zero_of_finite (by rw [← he]; rfl)

/-- `θ` is `H`-invariant. -/
theorem theta_conj (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index)
    (hχ : χ ∈ Irr H) (x : H) (z : Z) :
    θ ⟨x⁻¹ * z * x, by simpa using hZ.conj_mem z z.2 x⁻¹⟩ = θ z := by
  have h1 := congrFun hres z
  have h2 := congrFun hres ⟨x⁻¹ * z * x, by simpa using hZ.conj_mem z z.2 x⁻¹⟩
  simp only [pull_apply, Subgroup.coe_subtype, Pi.smul_apply, smul_eq_mul] at h1 h2
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast e_ne_zero he
  have h3 : χ (x⁻¹ * z * x) = χ z := (irr_isClassFn hχ).conj_eq _ _
  rw [h2, h1] at h3
  exact mul_left_cancel₀ he0 h3

variable {K R : Subgroup H}

theorem θD_mem_irr (hθ : θ ∈ Irr Z) (hZR : Z ≤ R) (hZK : Z ≤ K) :
    θD (K := K) (R := R) θ ∈ Irr (ZD K R Z) := by
  rw [θD_eq θ hZR hZK]; exact irr_pull_mulEquiv _ hθ

theorem θD_inv (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (hχ : χ ∈ Irr H) :
    IsInvariant (G := DD K R) (θD (K := K) (R := R) θ) := by
  intro d
  funext w
  simp only [conjN_apply, θD]
  have := theta_conj hres he hχ (ιDH K R d) ⟨ιDH K R w, w.2⟩
  convert this using 2
  ext; simp [ιDH]

/-- `Θ_D(φ) = ⟨φ_Z, θ⟩`. -/
theorem thetaPair_sD (hZR : Z ≤ R) (hZK : Z ≤ K) (φ : DD K R → ℂ) :
    thetaPair θ (sD hZR hZK) φ = ip (pull (ZD K R Z).subtype φ) (θD θ) := by
  have hc : Nat.card (ZD K R Z) = Nat.card Z := Nat.card_congr (eZD hZR hZK).toEquiv
  simp only [thetaPair, ip, hc]
  congr 1
  refine (Fintype.sum_equiv (eZD hZR hZK).toEquiv _ _ (fun w => ?_)).symm
  simp only [pull_apply, Subgroup.coe_subtype, θD]
  rfl

end Main

end

end CFSGOutside.Gagola

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

section Core

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [hZ : Z.Normal] {χ : H → ℂ} {θ : Z → ℂ}
  {e : ℕ} {K R : Subgroup H} [hK : K.Normal]

/-- Degrees are constant on orbits. -/
theorem conjN_one_apply {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal] (x : A)
    (σ : N → ℂ) : conjN N x σ 1 = σ 1 := by
  simp only [conjN_apply]
  congr 1; ext; simp

theorem mem_orbitF_one {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal] {σ τ : N → ℂ}
    (hτ : τ ∈ orbitF (A := A) σ) : τ 1 = σ 1 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hτ
  exact conjN_one_apply x σ

theorem mem_orbitF_self {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal]
    (σ : N → ℂ) : σ ∈ orbitF (A := A) σ :=
  Finset.mem_image.mpr ⟨1, Finset.mem_univ _, conjN_one σ⟩

theorem orbitF_conjN {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal] {σ τ : N → ℂ}
    (hτ : τ ∈ orbitF (A := A) σ) (x : A) : conjN N x τ ∈ orbitF (A := A) σ := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hτ
  exact Finset.mem_image.mpr ⟨x * y, Finset.mem_univ _, conjN_mul x y σ⟩

theorem orbitF_eq_of_mem {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal]
    {σ τ : N → ℂ} (hτ : τ ∈ orbitF (A := A) σ) : orbitF (A := A) τ = orbitF (A := A) σ := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hτ
  ext ρ
  simp only [orbitF, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x * y, (conjN_mul x y σ)⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x * y⁻¹, ?_⟩
    rw [← conjN_mul, inv_mul_cancel_right]

/-- The multiplicity of `σ` in a class function is preserved by simultaneous conjugation. -/
theorem mult_conjN_conjN {A : Type*} [Group A] [Fintype A] {N : Subgroup A} [N.Normal] (x : A)
    (f σ : N → ℂ) : mult (conjN N x f) (conjN N x σ) = mult f σ := by
  unfold mult; rw [ip_conjN]

/-- **The data behind Gagola's Corollary 3.6 and Lemma 4.4.** If `χ_K` has two different
constituents, then `D = R ∩ K` has a special element `g ∉ Z` (for `θ`), which is fused in `K` only
into its own `D`-class modulo `Z`. -/
theorem exists_special_of_two (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (hZK : Z ≤ K) (hZR : Z ≤ R)
    {p k : ℕ} [hp : Fact p.Prime] (hRZ : Nat.card R = p ^ k * Nat.card Z) (hpR : ¬ p ∣ R.index)
    (hKR : ∀ h : H, ∃ x ∈ K, ∃ r ∈ R, h = x * r)
    {τ₁ τ₂ : K → ℂ} (hτ₁ : τ₁ ∈ Irr K) (hτ₂ : τ₂ ∈ Irr K)
    (hm₁ : mult (pull K.subtype χ) τ₁ ≠ 0) (hm₂ : mult (pull K.subtype χ) τ₂ ≠ 0) (hne : τ₁ ≠ τ₂) :
    (∃ g : DD K R, IsSpecial (θD (K := K) (R := R) θ) g ∧ g ∉ ZD K R Z) ∧
      (∀ φ₀ ∈ spanOver (G := DD K R) (θD (K := K) (R := R) θ),
        ∃ f : K → ℂ, IsClassFn f ∧ pull (ιDK K R) f = φ₀) ∧
      ∀ T : Finset (DD K R), (∀ x ∈ T, IsSpecial (θD (K := K) (R := R) θ) x) →
        (∀ x ∈ T, ∀ y ∈ T, (∃ u : DD K R, u⁻¹ * y * u * x⁻¹ ∈ ZD K R Z) → x = y) →
        T.card ≤ (DD K R).index := by
  classical
  set D := DD K R
  have hD : D.Normal := hK.subgroupOf R
  -- `χ_R = a ζ`
  obtain ⟨ζ, hζ, a, hχR, ha⟩ := fr_sylow hχ hθ hres he hZR hp.out hRZ hpR
  have ha0 : a ≠ 0 := by
    rintro rfl; exact R.index_ne_zero_of_finite (by rw [← ha]; rfl)
  have hχD : pull (ιDH K R) χ = (a : ℂ) • pull D.subtype ζ := by
    funext l
    have := congrFun hχR (D.subtype l)
    simpa [ιDH] using this
  -- a constituent `σ₁` of `ζ_D`, and its `R`-orbit `X`
  have hζD := (irr_isNatComb hζ).pull D.subtype
  obtain ⟨σ₁, hσ₁, hb⟩ := exists_constituent hζD (by
    obtain ⟨d, hd, hd'⟩ := irr_one hζ
    simp only [pull_apply, map_one, hd']
    exact_mod_cast hd.ne')
  set X := orbitF (A := R) σ₁ with hXdef
  have hχDnat : IsNatComb (pull (ιDH K R) χ) := (irr_isNatComb hχ).pull _
  have hmultD : ∀ φ ∈ Irr D, mult (pull (ιDH K R) χ) φ = a * mult (pull D.subtype ζ) φ := by
    intro φ hφ; rw [hχD]; exact mult_nsmul hζD a hφ
  have hXchar : ∀ φ, φ ∈ X ↔ φ ∈ Irr D ∧ mult (pull (ιDH K R) χ) φ ≠ 0 := by
    intro φ
    constructor
    · intro hφ
      have hφI := orbitF_subset_irr hσ₁ φ hφ
      refine ⟨hφI, ?_⟩
      rw [hmultD φ hφI, mult_res_eq hζ hσ₁ hb hφ]
      exact Nat.mul_ne_zero ha0 hb
    · rintro ⟨hφI, hφ0⟩
      rw [hmultD φ hφI] at hφ0
      have : mult (pull D.subtype ζ) φ ≠ 0 := fun h0 => hφ0 (by rw [h0, mul_zero])
      obtain ⟨x, rfl⟩ := clifford_conj hζ hσ₁ hb hφI this
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  -- `Θ` on `D` and on `K`
  have hsD : ∀ z : Z, ιDH K R (sD hZR hZK z) = z := fun z => rfl
  have hsK : ∀ z : Z, K.subtype (Subgroup.inclusion hZK z) = z := fun z => rfl
  have hDc : (Nat.card D : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hKc : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have heZ : (e : ℂ) * Nat.card Z ≠ 0 := by
    have : (e : ℂ) ≠ 0 := by exact_mod_cast e_ne_zero he
    have hZc : (Nat.card Z : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact mul_ne_zero this hZc
  have hΘD : ∀ φ ∈ Irr D, thetaPair θ (sD hZR hZK) φ =
      (mult (pull (ιDH K R) χ) φ : ℂ) * (Nat.card D / (e * Nat.card Z)) := by
    intro φ hφ
    have h1 := fr_ip_pull_mul hχ hθ hres he (ιDH K R) (ιDH_injective K R) (sD hZR hZK) hsD φ
    rw [← hχDnat.mult_eq hφ] at h1
    rw [mul_div_assoc', eq_div_iff heZ]
    linear_combination h1.symm
  have hΘK : ∀ τ ∈ Irr K, thetaPair θ (Subgroup.inclusion hZK) τ =
      (mult (pull K.subtype χ) τ : ℂ) * (Nat.card K / (e * Nat.card Z)) := by
    intro τ hτ
    have h1 := fr_ip_pull_mul hχ hθ hres he K.subtype (Subgroup.subtype_injective K)
      (Subgroup.inclusion hZK) hsK τ
    rw [← ((irr_isNatComb hχ).pull K.subtype).mult_eq hτ] at h1
    rw [mul_div_assoc', eq_div_iff heZ]
    linear_combination h1.symm
  -- the orbit `O` of constituents of `χ_K`
  have hχK := (irr_isNatComb hχ).pull K.subtype
  set O := orbitF (A := H) τ₁ with hOdef
  have hOchar : ∀ τ, τ ∈ O ↔ τ ∈ Irr K ∧ mult (pull K.subtype χ) τ ≠ 0 := by
    intro τ
    constructor
    · intro hτ
      exact ⟨orbitF_subset_irr hτ₁ τ hτ, by rw [mult_res_eq hχ hτ₁ hm₁ hτ]; exact hm₁⟩
    · rintro ⟨hτI, hτ0⟩
      obtain ⟨x, rfl⟩ := clifford_conj hχ hτ₁ hm₁ hτI hτ0
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  -- `Θ_K(τ) = Θ_D(τ_D)`, and constituents
  have hjs : ∀ z : Z, ιDK K R (sD hZR hZK z) = Subgroup.inclusion hZK z := fun z => rfl
  have hpullDK : pull (ιDK K R) (pull K.subtype χ) = pull (ιDH K R) χ := rfl
  set c := (Nat.card D : ℂ) / (e * Nat.card Z) with hc
  have hc0 : c ≠ 0 := div_ne_zero hDc heZ
  have hc'0 : (Nat.card K : ℂ) / (e * Nat.card Z) ≠ 0 := div_ne_zero hKc heZ
  have hΘnat : ∀ f : D → ℂ, IsNatComb f → thetaPair θ (sD hZR hZK) f =
      ((∑ φ ∈ irrFinset D, mult f φ * mult (pull (ιDH K R) χ) φ : ℕ) : ℂ) * c := by
    intro f hf
    conv_lhs => rw [hf.eq_sum]
    rw [thetaPair_sum, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [thetaPair_smul, hΘD φ (mem_irrFinset.mp hφ)]
    push_cast; ring
  have hS5 : ∀ τ ∈ Irr K, mult (pull (ιDK K R) τ) σ₁ ≠ 0 → τ ∈ O := by
    intro τ hτ hτ0
    rw [hOchar]
    refine ⟨hτ, fun h0 => ?_⟩
    have h1 := hΘK τ hτ
    rw [h0, Nat.cast_zero, zero_mul, ← thetaPair_pull (sD hZR hZK) (Subgroup.inclusion hZK)
      (ιDK K R) hjs, hΘnat _ ((irr_isNatComb hτ).pull _)] at h1
    have hpos : 0 < ∑ φ ∈ irrFinset D, mult (pull (ιDK K R) τ) φ * mult (pull (ιDH K R) χ) φ := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun φ =>
        mult (pull (ιDK K R) τ) φ * mult (pull (ιDH K R) χ) φ) (fun _ _ => Nat.zero_le _)
        (mem_irrFinset.mpr hσ₁))
      exact Nat.mul_pos (Nat.pos_of_ne_zero hτ0)
        (Nat.pos_of_ne_zero ((hXchar σ₁).mp (mem_orbitF_self σ₁)).2)
    have := mul_eq_zero.mp h1
    rcases this with h | h
    · exact hpos.ne' (by exact_mod_cast h)
    · exact hc0 h
  have hS6 : ∀ τ ∈ O, ∀ φ ∈ Irr D, mult (pull (ιDK K R) τ) φ ≠ 0 → φ ∈ X := by
    intro τ hτ φ hφ hφ0
    obtain ⟨hτI, hτ0⟩ := (hOchar τ).mp hτ
    have hle : CharLE τ (pull K.subtype χ) :=
      charLE_of_mult_pos hχK hτI (Nat.one_le_iff_ne_zero.mpr hτ0)
    have hle' := hle.pull (ιDK K R)
    rw [hpullDK] at hle'
    have := hle'.mult_le ((irr_isNatComb hτI).pull _) hφ
    exact (hXchar φ).mpr ⟨hφ, by omega⟩
  -- degrees
  have hXdeg : ∀ φ ∈ X, φ 1 = σ₁ 1 := fun φ hφ => mem_orbitF_one hφ
  have hOdeg : ∀ τ ∈ O, τ 1 = τ₁ 1 := fun τ hτ => mem_orbitF_one hτ
  have hτ₁O : τ₁ ∈ O := mem_orbitF_self τ₁
  have hτ₂O : τ₂ ∈ O := (hOchar τ₂).mpr ⟨hτ₂, hm₂⟩
  -- the count `|K| = |D| (∑ a) (∑ b)`
  set aτ : (K → ℂ) → ℕ := fun τ => mult (pull (ιDK K R) τ) σ₁ with haτ
  set bφ : (D → ℂ) → ℕ := fun φ => mult (pull (ιDK K R) τ₁) φ with hbφ
  have hcount : Nat.card K = Nat.card D * ((∑ τ ∈ O, aτ τ) * (∑ φ ∈ X, bφ φ)) := by
    have hind := (irr_isNatComb hσ₁).indHom (ιDK_injective K R)
    have hind1 : indHom (ιDK K R) σ₁ 1 = (Nat.card D : ℂ)⁻¹ * Nat.card K * σ₁ 1 := by
      simp only [indHom, mul_one, mul_inv_cancel]
      rw [← map_one (ιDK K R), Finset.sum_congr rfl fun x _ =>
        (ιDK_injective K R).extend_apply σ₁ 0 1, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card (α := K)]
      ring
    have hmultind : ∀ ψ ∈ Irr K, mult (indHom (ιDK K R) σ₁) ψ = aτ ψ := by
      intro ψ hψ
      have h1 := hind.mult_eq hψ
      rw [ip_indHom (ιDK_injective K R) σ₁ (irr_isClassFn hψ), ip_comm,
        ← ((irr_isNatComb hψ).pull _).mult_eq hσ₁] at h1
      exact_mod_cast h1
    have hsum1 : indHom (ιDK K R) σ₁ 1 = ((∑ τ ∈ O, aτ τ : ℕ) : ℂ) * τ₁ 1 := by
      conv_lhs => rw [hind.eq_sum]
      rw [Finset.sum_apply]
      rw [← Finset.sum_subset (fun τ hτ => mem_irrFinset.mpr ((hOchar τ).mp hτ).1)]
      · rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ hτ => ?_
        rw [Pi.smul_apply, smul_eq_mul, hmultind τ ((hOchar τ).mp hτ).1, hOdeg τ hτ]
      · intro τ hτ hτO
        have : aτ τ = 0 := by
          by_contra h0; exact hτO (hS5 τ (mem_irrFinset.mp hτ) h0)
        rw [Pi.smul_apply, hmultind τ (mem_irrFinset.mp hτ), this]; simp
    have hsum2 : τ₁ 1 = ((∑ φ ∈ X, bφ φ : ℕ) : ℂ) * σ₁ 1 := by
      have hf := (irr_isNatComb hτ₁).pull (ιDK K R)
      have h1 : pull (ιDK K R) τ₁ 1 = τ₁ 1 := by simp [pull_apply]
      rw [← h1, hf.eq_sum, Finset.sum_apply]
      rw [← Finset.sum_subset (fun φ hφ => mem_irrFinset.mpr (orbitF_subset_irr hσ₁ φ hφ))]
      · rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun φ hφ => ?_
        rw [Pi.smul_apply, smul_eq_mul, hXdeg φ hφ]
      · intro φ hφ hφX
        have : bφ φ = 0 := by
          by_contra h0; exact hφX (hS6 τ₁ hτ₁O φ (mem_irrFinset.mp hφ) h0)
        rw [Pi.smul_apply]; simp [hbφ] at this; rw [this]; simp
    have hσ0 : σ₁ 1 ≠ 0 := by
      obtain ⟨d, hd, hd'⟩ := irr_one hσ₁; rw [hd']; exact_mod_cast hd.ne'
    rw [hind1, hsum2] at hsum1
    have : (Nat.card K : ℂ) = Nat.card D * (((∑ τ ∈ O, aτ τ : ℕ) : ℂ) * ((∑ φ ∈ X, bφ φ : ℕ) : ℂ)) := by
      have h2 := mul_right_cancel₀ hσ0 (by linear_combination hsum1 :
        (Nat.card D : ℂ)⁻¹ * Nat.card K * σ₁ 1 =
          (((∑ τ ∈ O, aτ τ : ℕ) : ℂ) * ((∑ φ ∈ X, bφ φ : ℕ) : ℂ)) * σ₁ 1)
      field_simp at h2
      linear_combination h2
    exact_mod_cast this
  -- `|K| = |H : R| |D|`, so `(∑ a)(∑ b) = |H : R|` is prime to `p`
  have hsup : R ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨x, hx, r, hr, rfl⟩ := hKR h
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hr)
  have hKidx : K.index = D.index := by
    have := Subgroup.relIndex_sup_right R K
    rw [hsup, Subgroup.relIndex_top_right] at this
    exact this
  have hcardKD : Nat.card K = R.index * Nat.card D := by
    have h1 := K.card_mul_index
    have h2 := R.card_mul_index
    have h3 := D.card_mul_index
    have hDi : 0 < D.index := Nat.pos_of_ne_zero D.index_ne_zero_of_finite
    rw [hKidx] at h1
    refine Nat.eq_of_mul_eq_mul_right hDi ?_
    calc Nat.card K * D.index = Nat.card H := h1
      _ = Nat.card R * R.index := h2.symm
      _ = Nat.card D * D.index * R.index := by rw [h3]
      _ = R.index * Nat.card D * D.index := by ring
  have hab_eq : (∑ τ ∈ O, aτ τ) * (∑ φ ∈ X, bφ φ) = R.index := by
    have hD0 : 0 < Nat.card D := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hD0 ?_
    rw [← hcount, hcardKD, mul_comm]
  have hpa : ¬ p ∣ ∑ τ ∈ O, aτ τ := fun h => hpR (hab_eq ▸ Dvd.dvd.mul_right h _)
  have hpb : ¬ p ∣ ∑ φ ∈ X, bφ φ := fun h => hpR (hab_eq ▸ Dvd.dvd.mul_left h _)
  -- `R / D` is a `p`-group
  have hRD : ∀ r : R, (r ^ p ^ k : R) ∈ D := by
    intro r
    have hZD : Nat.card Z ∣ Nat.card D := by
      have hc : Nat.card (ZD K R Z) = Nat.card Z := Nat.card_congr (eZD hZR hZK).toEquiv
      rw [← hc]; exact Subgroup.card_subgroup_dvd_card (ZD K R Z)
    have hquot : Nat.card (R ⧸ D) ∣ p ^ k := by
      obtain ⟨m, hm⟩ := hZD
      have h1 := D.card_mul_index
      rw [Subgroup.index_eq_card] at h1
      have hZ0 : 0 < Nat.card Z := Nat.card_pos
      refine ⟨m, Nat.eq_of_mul_eq_mul_right hZ0 ?_⟩
      calc p ^ k * Nat.card Z = Nat.card R := hRZ.symm
        _ = Nat.card D * Nat.card (R ⧸ D) := h1.symm
        _ = Nat.card (R ⧸ D) * m * Nat.card Z := by rw [hm]; ring
    obtain ⟨t, ht⟩ := hquot
    have h1 : ((r : R ⧸ D)) ^ Nat.card (R ⧸ D) = 1 := pow_card_eq_one'
    have h2 : ((r ^ p ^ k : R) : R ⧸ D) = 1 := by
      rw [QuotientGroup.mk_pow, ht, pow_mul, h1, one_pow]
    exact (QuotientGroup.eq_one_iff _).mp h2
  -- a fixed point `τ⋆` of the inertia group `J` of `σ₁`, with `a(τ⋆) ≠ 0`
  set J := inertia (N := D) σ₁ with hJ
  have hconjDK : ∀ (r : R) (τ : K → ℂ),
      pull (ιDK K R) (conjN K (r : H) τ) = conjN D r (pull (ιDK K R) τ) := by
    intro r τ; funext d; simp only [pull_apply, conjN_apply]; congr 1
  letI actJ : MulAction J {τ // τ ∈ O} :=
    { smul j τ := ⟨conjN K (((j : R) : H)) τ.1, orbitF_conjN τ.2 _⟩
      one_smul τ := Subtype.ext (conjN_one τ.1)
      mul_smul j j' τ := Subtype.ext (conjN_mul _ _ τ.1) }
  have hsmulJ : ∀ (j : J) (τ : {τ // τ ∈ O}), (j • τ).1 = conjN K (((j : R) : H)) τ.1 :=
    fun _ _ => rfl
  have hKfix : ∀ τ ∈ O, ∀ x : H, x ∈ K → conjN K x τ = τ := fun τ hτ x hx =>
    conjN_of_mem (irr_isClassFn ((hOchar τ).mp hτ).1) hx
  obtain ⟨τs, hτs0, hτsfix⟩ := exists_fixed_of_weight_sum (P := J) (α := {τ // τ ∈ O}) (p := p)
    (fun j => ⟨k, fun τ => Subtype.ext (by
      rw [hsmulJ]
      exact hKfix τ.1 τ.2 _ (Subgroup.mem_subgroupOf.mp (hRD (j : R))))⟩)
    (fun τ => aτ τ.1)
    (fun j τ => by
      simp only [haτ]
      rw [hsmulJ, hconjDK]
      conv_lhs => rw [← (mem_inertia.mp j.2 : conjN D (j : R) σ₁ = σ₁)]
      exact mult_conjN_conjN _ _ _)
    (by rwa [Finset.sum_coe_sort O (fun τ => aτ τ)])
  -- `|O| ≤ |X|`
  have hOX : O.card ≤ X.card := by
    have hO' : O = orbitF (A := H) τs.1 := (orbitF_eq_of_mem τs.2).symm
    have hsub : O ⊆ Finset.univ.image (fun q : R ⧸ J => conjN K (((q.out : R)) : H) τs.1) := by
      intro τ hτ
      rw [hO'] at hτ
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hτ
      obtain ⟨x, hx, r, hr, rfl⟩ := hKR h
      refine Finset.mem_image.mpr ⟨((⟨r, hr⟩ : R) : R ⧸ J), Finset.mem_univ _, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j : J, (((⟨r, hr⟩ : R) : R ⧸ J).out : R) = ⟨r, hr⟩ * j :=
        QuotientGroup.mk_out_eq_mul J ⟨r, hr⟩
      rw [hj, conjN_mul, Subgroup.coe_mul, conjN_mul]
      have h1 : conjN K (((j : R) : H)) τs.1 = τs.1 := by
        have := hτsfix j; rw [Subtype.ext_iff, hsmulJ] at this; exact this
      rw [h1, hKfix _ (orbitF_conjN τs.2 _) x hx]
    calc O.card ≤ (Finset.univ.image (fun q : R ⧸ J => conjN K (((q.out : R)) : H) τs.1)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (R ⧸ J)).card := Finset.card_image_le
      _ = J.index := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.index]
      _ = X.card := index_inertia σ₁
  -- two different elements of `X`
  have hO2 : 1 < O.card := Finset.one_lt_card.mpr ⟨τ₁, hτ₁O, τ₂, hτ₂O, hne⟩
  obtain ⟨σ', hσ'X, hσ'ne⟩ := Finset.exists_mem_ne (lt_of_lt_of_le hO2 hOX) σ₁
  -- elements of `X` lie over `θ_D`
  have hover : ∀ φ ∈ X, mult (pull (ZD K R Z).subtype φ) (θD θ) ≠ 0 := by
    intro φ hφ h0
    obtain ⟨hφI, hφ0⟩ := (hXchar φ).mp hφ
    have h1 := ((irr_isNatComb hφI).pull (ZD K R Z).subtype).mult_eq (θD_mem_irr hθ hZR hZK)
    rw [h0, ← thetaPair_sD hZR hZK, hΘD φ hφI, Nat.cast_zero] at h1
    have := (mul_eq_zero.mp h1.symm).resolve_right hc0
    exact hφ0 (by exact_mod_cast this)
  -- a special element outside `Z`
  obtain ⟨g, hgsp, hgZ⟩ : ∃ g : D, IsSpecial (θD (K := K) (R := R) θ) g ∧ g ∉ ZD K R Z := by
    by_contra hall
    push Not at hall
    exact hσ'ne (irr_eq_of_special_le (θD_mem_irr hθ hZR hZK) (θD_inv hres he hχ) hall
      (orbitF_subset_irr hσ₁ σ' hσ'X) hσ₁ (hover σ' hσ'X) (hover σ₁ (mem_orbitF_self σ₁)))
  have hXsub : ∀ ψ ∈ (irrFinset D).filter
      (fun ψ => mult (pull (ZD K R Z).subtype ψ) (θD θ) ≠ 0), ψ ∈ X := by
    intro ψ hψ
    obtain ⟨hψI, hψ0⟩ := Finset.mem_filter.mp hψ
    have hψI' := mem_irrFinset.mp hψI
    refine (hXchar ψ).mpr ⟨hψI', fun h0 => hψ0 ?_⟩
    have h1 := ((irr_isNatComb hψI').pull (ZD K R Z).subtype).mult_eq (θD_mem_irr hθ hZR hZK)
    rw [← thetaPair_sD hZR hZK, hΘD ψ hψI', h0, Nat.cast_zero, zero_mul] at h1
    exact_mod_cast h1
  refine ⟨⟨g, hgsp, hgZ⟩, ?_, ?_⟩
  -- restriction from `K` onto the span of `Irr (D | θ)`, by the mod-`p` spanning lemma
  · letI actR : MulAction R {φ // φ ∈ X} :=
      { smul r φ := ⟨conjN D r φ.1, orbitF_conjN φ.2 _⟩
        one_smul φ := Subtype.ext (conjN_one φ.1)
        mul_smul r r' φ := Subtype.ext (conjN_mul _ _ φ.1) }
    have hsmulR : ∀ (r : R) (φ : {φ // φ ∈ X}), (r • φ).1 = conjN D r φ.1 := fun _ _ => rfl
    haveI : MulAction.IsPretransitive R {φ // φ ∈ X} := by
      refine ⟨fun φ φ' => ?_⟩
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp φ.2
      obtain ⟨y', -, hy'⟩ := Finset.mem_image.mp φ'.2
      refine ⟨y' * y⁻¹, Subtype.ext ?_⟩
      rw [hsmulR, ← hy, ← hy', ← conjN_mul, inv_mul_cancel_right]
    set t : {τ // τ ∈ O} → {φ // φ ∈ X} → ℤ := fun τ φ => (mult (pull (ιDK K R) τ.1) φ.1 : ℤ)
      with ht
    have hspan := span_eq_top_of_modp (p := p) (P := R) (X := {φ // φ ∈ X})
      (ι := {τ // τ ∈ O})
      (fun r => ⟨k, fun φ => Subtype.ext (by
        rw [hsmulR]
        exact conjN_of_mem (irr_isClassFn (orbitF_subset_irr hσ₁ _ φ.2)) (hRD r))⟩)
      t
      (fun r τ => ⟨⟨conjN K ((r : R) : H) τ.1, orbitF_conjN τ.2 _⟩, fun φ => by
        simp only [ht, hsmulR]
        rw [hconjDK]
        congr 1
        conv_lhs => rw [show φ.1 = conjN D r (conjN D r⁻¹ φ.1) by
          rw [← conjN_mul, mul_inv_cancel, conjN_one]]
        exact mult_conjN_conjN _ _ _⟩)
      ⟨⟨τ₁, hτ₁O⟩, by
        simp only [ht]
        rw [← Nat.cast_sum, Finset.sum_coe_sort X (fun φ => mult (pull (ιDK K R) τ₁) φ)]
        exact_mod_cast hpb⟩
    intro φ₀ hφ₀
    -- `φ₀` is a combination of `X`
    have hXsub : ∀ ψ ∈ (irrFinset D).filter
        (fun ψ => mult (pull (ZD K R Z).subtype ψ) (θD θ) ≠ 0), ψ ∈ X := by
      intro ψ hψ
      obtain ⟨hψI, hψ0⟩ := Finset.mem_filter.mp hψ
      have hψI' := mem_irrFinset.mp hψI
      refine (hXchar ψ).mpr ⟨hψI', fun h0 => hψ0 ?_⟩
      have h1 := ((irr_isNatComb hψI').pull (ZD K R Z).subtype).mult_eq (θD_mem_irr hθ hZR hZK)
      rw [← thetaPair_sD hZR hZK, hΘD ψ hψI', h0, Nat.cast_zero, zero_mul] at h1
      exact_mod_cast h1
    have hφ₀ip : ∀ ψ ∈ Irr D, ψ ∉ X → ip φ₀ ψ = 0 := by
      intro ψ hψ hψX
      induction hφ₀ using Submodule.span_induction with
      | mem x hx =>
        have hxX := hXsub x (Finset.mem_coe.mp hx)
        have hx' := mem_irrFinset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
        rw [ip_irr hx' hψ, if_neg (fun h => hψX (by rw [← h]; exact hxX))]
      | zero => exact ip_zero_left _
      | add x y _ _ hx hy => rw [ip_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [ip_smul_left, hx, mul_zero]
    have hφ₀eq : φ₀ = ∑ φ ∈ X, ip φ₀ φ • φ := by
      conv_lhs => rw [classFn_eq_sum (isClassFn_of_mem_spanOver hφ₀)]
      refine (Finset.sum_subset (fun φ hφ => mem_irrFinset.mpr (orbitF_subset_irr hσ₁ φ hφ))
        (fun ψ hψ hψX => by rw [hφ₀ip ψ (mem_irrFinset.mp hψ) hψX, zero_smul])).symm
    -- the coefficient vector lies in the span
    have hc : (fun φ : {φ // φ ∈ X} => ip φ₀ φ.1) ∈
        Submodule.span ℂ (Set.range fun i : {τ // τ ∈ O} => fun x => (t i x : ℂ)) := by
      rw [hspan]; trivial
    obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hc
    refine ⟨∑ i : {τ // τ ∈ O}, lam i • (i.1 : K → ℂ), ?_, ?_⟩
    · exact isClassFn_sum _ fun i _ =>
        isClassFn_smul _ (irr_isClassFn ((hOchar i.1).mp i.2).1)
    · rw [pull_sum]
      have hres_i : ∀ i : {τ // τ ∈ O}, pull (ιDK K R) i.1 =
          ∑ φ ∈ X, (mult (pull (ιDK K R) i.1) φ : ℂ) • φ := by
        intro i
        have hf := ((irr_isNatComb ((hOchar i.1).mp i.2).1)).pull (ιDK K R)
        conv_lhs => rw [hf.eq_sum]
        refine (Finset.sum_subset (fun φ hφ => mem_irrFinset.mpr (orbitF_subset_irr hσ₁ φ hφ))
          (fun ψ hψ hψX => ?_)).symm
        have : mult (pull (ιDK K R) i.1) ψ = 0 := by
          by_contra h0; exact hψX (hS6 i.1 i.2 ψ (mem_irrFinset.mp hψ) h0)
        rw [this, Nat.cast_zero, zero_smul]
      have e1 : ∑ i : {τ // τ ∈ O}, pull (ιDK K R) (lam i • (i.1 : K → ℂ)) =
          ∑ i : {τ // τ ∈ O}, ∑ φ ∈ X, (lam i * (mult (pull (ιDK K R) i.1) φ : ℂ)) • φ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [pull_smul, hres_i i, Finset.smul_sum]
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [smul_smul]
      rw [e1, Finset.sum_comm]
      conv_rhs => rw [hφ₀eq]
      refine Finset.sum_congr rfl fun φ hφ => ?_
      rw [← Finset.sum_smul]
      congr 1
      have := congrFun hlam ⟨φ, hφ⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht] at this
      exact this
  · intro T hT hdis
    have h1 := card_special_le (θD_mem_irr hθ hZR hZK) (θD_inv hres he hχ) T hT hdis
    have h2 := Finset.card_le_card (fun ψ hψ => hXsub ψ hψ)
    have h3 : X.card ∣ D.index := by
      rw [hXdef, ← index_inertia σ₁]
      exact Subgroup.index_dvd_of_le (le_inertia (irr_isClassFn hσ₁))
    exact h1.trans (h2.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero D.index_ne_zero_of_finite) h3))


end Core

section Final

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [hZ : Z.Normal] {χ : H → ℂ} {θ : Z → ℂ}
  {e : ℕ} {K R : Subgroup H} [hK : K.Normal]

/-- `|K| = |H : R| |R ∩ K|` when `H = K R`. -/
theorem card_eq_index_mul (hKR : ∀ h : H, ∃ x ∈ K, ∃ r ∈ R, h = x * r) :
    Nat.card K = R.index * Nat.card (DD K R) := by
  have hsup : R ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨x, hx, r, hr, rfl⟩ := hKR h
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hr)
  have hKidx : K.index = (DD K R).index := by
    have := Subgroup.relIndex_sup_right R K
    rw [hsup, Subgroup.relIndex_top_right] at this
    exact this
  have h1 := K.card_mul_index
  have h2 := R.card_mul_index
  have h3 := (DD K R).card_mul_index
  have hDi : 0 < (DD K R).index := Nat.pos_of_ne_zero (DD K R).index_ne_zero_of_finite
  rw [hKidx] at h1
  refine Nat.eq_of_mul_eq_mul_right hDi ?_
  calc Nat.card K * (DD K R).index = Nat.card H := h1
    _ = Nat.card R * R.index := h2.symm
    _ = Nat.card (DD K R) * (DD K R).index * R.index := by rw [h3]
    _ = R.index * Nat.card (DD K R) * (DD K R).index := by ring

theorem card_DD (K R : Subgroup H) : Nat.card (DD K R) = Nat.card (R.subgroupOf K) := by
  have e1 : Nat.card (DD K R) = Nat.card (R ⊓ K : Subgroup H) := by
    rw [show DD K R = (R ⊓ K).subgroupOf R from (Subgroup.inf_subgroupOf_left K R).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have e2 : Nat.card (R.subgroupOf K) = Nat.card (R ⊓ K : Subgroup H) := by
    rw [show R.subgroupOf K = (R ⊓ K).subgroupOf K from (Subgroup.inf_subgroupOf_right R K).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [e1, e2]

/-- **Gagola, Corollary 3.6** (the uniqueness of the constituent). Let `(H, Z, χ)` be fully ramified,
`Z ≤ K ⊴ H`, `R ≥ Z` with `R/Z` a Sylow `p`-subgroup of `H/Z` and `H = K R`. If `(R ∩ K)/Z` is
abelian and `K/Z` has no nontrivial `p`-group quotient, then `χ_K` has a single irreducible
constituent. -/
theorem cor_3_6 (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z)
    (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) (hZK : Z ≤ K) (hZR : Z ≤ R)
    {p k : ℕ} [hp : Fact p.Prime] (hRZ : Nat.card R = p ^ k * Nat.card Z) (hpR : ¬ p ∣ R.index)
    (hKR : ∀ h : H, ∃ x ∈ K, ∃ r ∈ R, h = x * r)
    (hab : ∀ a ∈ R ⊓ K, ∀ b ∈ R ⊓ K, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hno : ∀ (M : Subgroup (K ⧸ Z.subgroupOf K)) [M.Normal],
      IsPGroup p ((K ⧸ Z.subgroupOf K) ⧸ M) → M = ⊤)
    {τ₁ τ₂ : K → ℂ} (hτ₁ : τ₁ ∈ Irr K) (hτ₂ : τ₂ ∈ Irr K)
    (hm₁ : mult (pull K.subtype χ) τ₁ ≠ 0) (hm₂ : mult (pull K.subtype χ) τ₂ ≠ 0) : τ₁ = τ₂ := by
  by_contra hne
  obtain ⟨⟨g, hgsp, hgZ⟩, hsurj, -⟩ := exists_special_of_two hχ hθ hres he hZK hZR hRZ hpR hKR
    hτ₁ hτ₂ hm₁ hm₂ hne
  obtain ⟨m, hm⟩ := nonfusion (ιDK K R) (θD_mem_irr hθ hZR hZK) (θD_inv hres he hχ) hsurj hgsp
  set ZK := Z.subgroupOf K
  set X := K ⧸ ZK
  set Q : K →* X := QuotientGroup.mk' ZK
  have hQ1 : ∀ x : K, Q x = 1 ↔ (x : H) ∈ Z := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set P0 : Subgroup K := R.subgroupOf K
  set P : Subgroup X := P0.map Q
  -- `P` is a Sylow `p`-subgroup
  have hRp : ∀ x : H, x ∈ R → x ^ p ^ k ∈ Z := by
    intro x hx
    have hc : Nat.card (R ⧸ Z.subgroupOf R) = p ^ k := by
      have h1 := (Z.subgroupOf R).card_mul_index
      rw [Subgroup.index_eq_card] at h1
      have hZc : Nat.card (Z.subgroupOf R) = Nat.card Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
      rw [hZc, hRZ, mul_comm] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h2 : ((⟨x, hx⟩ : R) : R ⧸ Z.subgroupOf R) ^ p ^ k = 1 := by
      rw [← hc]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hPp : IsPGroup p P := by
    rintro ⟨y, x, hx, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hQ1]
    simpa using hRp _ (Subgroup.mem_subgroupOf.mp hx)
  have hPidx : ¬ p ∣ P.index := by
    have hker : Q.ker ≤ P0 := by
      intro x hx
      rw [MonoidHom.mem_ker, hQ1] at hx
      exact Subgroup.mem_subgroupOf.mpr (hZR hx)
    rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective ZK) hker]
    have h1 := P0.card_mul_index
    rw [card_eq_index_mul hKR, ← card_DD] at h1
    have hD0 : 0 < Nat.card (DD K R) := Nat.card_pos
    have : P0.index = R.index := by
      refine Nat.eq_of_mul_eq_mul_left hD0 ?_
      rw [h1]; ring
    rw [this]; exact hpR
  set S : Sylow p X := hPp.toSylow hPidx
  have hS : (S : Subgroup X) = P := rfl
  -- `P` is abelian
  have hPab : IsMulCommutative (S : Subgroup X) := by
    refine ⟨⟨fun y₁ y₂ => Subtype.ext ?_⟩⟩
    obtain ⟨x₁, hx₁, h₁⟩ := y₁.2
    obtain ⟨x₂, hx₂, h₂⟩ := y₂.2
    simp only [Subgroup.coe_mul]
    rw [← h₁, ← h₂, ← map_mul, ← map_mul]
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hQ1]
    have := hab _ ⟨Subgroup.mem_subgroupOf.mp hx₁, x₁.2⟩ _ ⟨Subgroup.mem_subgroupOf.mp hx₂, x₂.2⟩
    simpa [mul_assoc] using this
  -- the element `c`
  set c := Q (ιDK K R g)
  have hcP : c ∈ (S : Subgroup X) := ⟨ιDK K R g, Subgroup.mem_subgroupOf.mpr (g : R).2, rfl⟩
  have hc1 : c ≠ 1 := by
    rw [Ne, hQ1]; exact hgZ
  have hcN : ∀ n ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), n * c = c * n := by
    intro n hn
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ZK n
    set y : K := ιDK K R (g * m)
    have hy : Q (x * y * x⁻¹) ∈ P := by
      have hyP : Q y ∈ P := ⟨y, Subgroup.mem_subgroupOf.mpr ((g * m : DD K R) : R).2, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hn (Q y)).mp hyP
      rw [map_mul, map_mul, map_inv]
      exact this
    obtain ⟨w, hw, hwy⟩ := hy
    have hxyR : ((x * y * x⁻¹ : K) : H) ∈ R := by
      have h1 : Q (w⁻¹ * (x * y * x⁻¹)) = 1 := by rw [map_mul, map_inv, hwy, inv_mul_cancel]
      rw [hQ1] at h1
      have := R.mul_mem (Subgroup.mem_subgroupOf.mp hw) (hZR h1)
      simpa [mul_assoc] using this
    set d' : DD K R := ⟨⟨(x * y * x⁻¹ : K), hxyR⟩, Subgroup.mem_subgroupOf.mpr (x * y * x⁻¹).2⟩
    obtain ⟨u, hu⟩ := hm x d' rfl
    have hu' : ((u : R) : H)⁻¹ * (x * y * x⁻¹ : K) * (u : R) * ((g : R) : H)⁻¹ ∈ Z := hu
    have hug : ((u : R) : H) * (g : R) * ((u : R) : H)⁻¹ * ((g : R) : H)⁻¹ ∈ Z :=
      hab _ ⟨(u : R).2, Subgroup.mem_subgroupOf.mp u.2⟩ _ ⟨(g : R).2, Subgroup.mem_subgroupOf.mp g.2⟩
    have hmZ : (((m : DD K R) : R) : H) ∈ Z := m.2
    -- `x g x⁻¹ g⁻¹ ∈ Z`
    have hxg : (x : H) * (g : R) * (x : H)⁻¹ * ((g : R) : H)⁻¹ ∈ Z := by
      have e1 : (x : H) * (g : R) * (x : H)⁻¹ * ((g : R) : H)⁻¹ =
          ((u : R) : H) * (((u : R) : H)⁻¹ * (x * y * x⁻¹ : K) * (u : R) * ((g : R) : H)⁻¹) *
            ((u : R) : H)⁻¹ *
          (((u : R) : H) * (g : R) * ((u : R) : H)⁻¹ * ((g : R) : H)⁻¹) *
          (((g : R) : H) * ((x : H) * ((((m : DD K R) : R) : H))⁻¹ * (x : H)⁻¹) *
            ((g : R) : H)⁻¹) := by
        simp only [y, ιDK_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e1]
      refine Z.mul_mem (Z.mul_mem ?_ hug) ?_
      · have := hZ.conj_mem _ hu' ((u : R) : H); simpa [mul_assoc] using this
      · have := hZ.conj_mem _ (hZ.conj_mem _ (Z.inv_mem hmZ) (x : H)) ((g : R) : H)
        simpa [mul_assoc] using this
    rw [← mul_inv_eq_one]
    show Q x * Q (ιDK K R g) * (Q (ιDK K R g) * Q x)⁻¹ = 1
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, hQ1]
    simpa [mul_assoc] using hxg
  obtain ⟨M, hMn, hMtop, hMp⟩ := exists_pQuotient_of_central S hPab hcP hc1 hcN
  exact hMtop (@hno M hMn hMp)

end Final

end

end CFSGOutside.Gagola
