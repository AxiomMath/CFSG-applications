import CFSGOutside.Gagola.FullyRamified

/-!
# Gagola, Lemma 2.3 (parts (a) and (c))

Let `(H, Z, χ)` be a fully ramified triple, `Z ≤ K ⊴ H`, `p` a prime and `R ≥ Z` with `|R : Z|` a power
of `p` and `p ∤ |H : R|`. Let `ζ` be the constituent of `χ_R` (Lemma 2.2), `σ` an irreducible constituent
of `ζ_{R ∩ K}`, with multiplicity `b`, and `s` the number of `R`-conjugates of `σ`. Then

* (a) `b² s = |R : R ∩ K|`, and `σ` has a character `φ` of its inertia group in `R` with `φ_{R ∩ K} = b σ`;
* (c) `H` has a subgroup `T ≥ K` of index `s`.

`R ∩ K` is `K.subgroupOf R`, a normal subgroup of `R`. Part (c) uses the Frattini argument, given as the
hypothesis `(NN R K) ⊔ K = ⊤`, and that `|K : R ∩ K|` is prime to `p`.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

variable {H : Type*} [Group H] [Fintype H]

section ExtConj

/-- The normalizer of `R ∩ K`. -/
abbrev NN (R K : Subgroup H) : Subgroup H := Subgroup.normalizer ((R ⊓ K : Subgroup H) : Set H)

variable (R K : Subgroup H)

theorem conj_inv_mem_inf {x : H} (hx : x ∈ (NN R K)) {y : H} (hy : y ∈ R ⊓ K) :
    x⁻¹ * y * x ∈ R ⊓ K := by
  have := (Subgroup.mem_normalizer_iff.mp ((NN R K).inv_mem hx) y).mp hy
  simpa using this

theorem mem_inf_of_subgroupOf (l : K.subgroupOf R) : ((l : R) : H) ∈ R ⊓ K :=
  ⟨(l : R).2, Subgroup.mem_subgroupOf.mp l.2⟩

/-- The element `x⁻¹ l x` of `R ∩ K`, for `x` normalizing `R ∩ K`. -/
def conjSub {x : H} (hx : x ∈ (NN R K)) (l : K.subgroupOf R) : K.subgroupOf R :=
  ⟨⟨x⁻¹ * ((l : R) : H) * x, (conj_inv_mem_inf R K hx (mem_inf_of_subgroupOf R K l)).1⟩,
    Subgroup.mem_subgroupOf.mpr (conj_inv_mem_inf R K hx (mem_inf_of_subgroupOf R K l)).2⟩

@[simp] theorem coe_conjSub {x : H} (hx : x ∈ (NN R K)) (l : K.subgroupOf R) :
    ((conjSub R K hx l : R) : H) = x⁻¹ * ((l : R) : H) * x := rfl

/-- `l ↦ x⁻¹ l x` as an automorphism of `R ∩ K`. -/
def conjSubAut {x : H} (hx : x ∈ (NN R K)) : K.subgroupOf R ≃* K.subgroupOf R where
  toFun := conjSub R K hx
  invFun := conjSub R K ((NN R K).inv_mem hx)
  left_inv l := by ext; simp; group
  right_inv l := by ext; simp; group
  map_mul' l l' := by ext; simp; group

/-- External conjugation of a function on `R ∩ K` by an element normalizing `R ∩ K`. -/
def extConj {x : H} (hx : x ∈ (NN R K)) (τ : K.subgroupOf R → ℂ) : K.subgroupOf R → ℂ :=
  pull (conjSubAut R K hx).toMonoidHom τ

@[simp] theorem extConj_apply {x : H} (hx : x ∈ (NN R K)) (τ : K.subgroupOf R → ℂ)
    (l : K.subgroupOf R) : extConj R K hx τ l = τ (conjSub R K hx l) := rfl

theorem extConj_mem_irr {x : H} (hx : x ∈ (NN R K)) {τ : K.subgroupOf R → ℂ}
    (hτ : τ ∈ Irr _) : extConj R K hx τ ∈ Irr _ := irr_pull_mulEquiv _ hτ

theorem extConj_one (τ : K.subgroupOf R → ℂ) : extConj R K ((NN R K).one_mem) τ = τ := by
  funext l; simp only [extConj_apply]; congr 1; ext; simp

theorem extConj_mul {x y : H} (hx : x ∈ (NN R K)) (hy : y ∈ (NN R K))
    (τ : K.subgroupOf R → ℂ) :
    extConj R K ((NN R K).mul_mem hx hy) τ = extConj R K hx (extConj R K hy τ) := by
  funext l; simp only [extConj_apply]; congr 1; ext; simp; group

theorem le_normalizer_inf [K.Normal] : R ≤ (NN R K) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyR, hyK⟩
    exact ⟨R.mul_mem (R.mul_mem hr hyR) (R.inv_mem hr), ‹K.Normal›.conj_mem y hyK r⟩
  · rintro ⟨hyR, hyK⟩
    refine ⟨?_, ?_⟩
    · have := R.mul_mem (R.mul_mem (R.inv_mem hr) hyR) hr
      simpa [mul_assoc] using this
    · have := ‹K.Normal›.conj_mem _ hyK r⁻¹
      simpa [mul_assoc] using this

theorem inf_le_normalizer : R ⊓ K ≤ NN R K := Subgroup.le_normalizer

/-- For `r ∈ R`, external conjugation is the conjugation of Clifford theory in `R`. -/
theorem extConj_eq_conjN [K.Normal] {r : H} (hr : r ∈ R) (τ : K.subgroupOf R → ℂ) :
    extConj R K (le_normalizer_inf R K hr) τ = conjN (K.subgroupOf R) (⟨r, hr⟩ : R) τ := by
  funext l
  simp only [extConj_apply, conjN_apply]
  congr 1

/-- For `m ∈ R ∩ K`, external conjugation fixes class functions. -/
theorem extConj_of_mem_inf {m : H} (hm : m ∈ R ⊓ K) {τ : K.subgroupOf R → ℂ} (hτ : IsClassFn τ) :
    extConj R K (inf_le_normalizer R K hm) τ = τ := by
  funext l
  simp only [extConj_apply]
  have := hτ.conj_eq l ⟨⟨m, hm.1⟩, Subgroup.mem_subgroupOf.mpr hm.2⟩
  convert this using 2
  ext; simp

/-- External conjugation preserves the multiplicities in the restriction of a class function of `H`. -/
theorem mult_extConj {χ : H → ℂ} (hχ : IsClassFn χ) {x : H} (hx : x ∈ (NN R K))
    (τ : K.subgroupOf R → ℂ) :
    mult (pull (R.subtype.comp (K.subgroupOf R).subtype) χ) (extConj R K hx τ) =
      mult (pull (R.subtype.comp (K.subgroupOf R).subtype) χ) τ := by
  have hfix : pull (conjSubAut R K hx).toMonoidHom (pull (R.subtype.comp (K.subgroupOf R).subtype) χ) =
      pull (R.subtype.comp (K.subgroupOf R).subtype) χ := by
    funext l
    simp only [pull_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
    show χ (x⁻¹ * ((l : R) : H) * x) = χ ((l : R) : H)
    exact hχ.conj_eq _ x
  unfold mult extConj
  conv_lhs => rw [← hfix]
  rw [ip_pull_mulEquiv]

end ExtConj

section Frattini

/-- The action of the normalizer of `R ∩ K` on an `R`-orbit `Ω` of characters that it preserves. -/
abbrev omegaAction (R K : Subgroup H) (Ω : Finset (K.subgroupOf R → ℂ))
    (hΩ : ∀ x (hx : x ∈ (NN R K)), ∀ τ ∈ Ω, extConj R K hx τ ∈ Ω) :
    MulAction (NN R K) {τ // τ ∈ Ω} where
  smul x τ := ⟨extConj R K x.2 τ.1, hΩ x x.2 τ.1 τ.2⟩
  one_smul τ := Subtype.ext (extConj_one R K τ.1)
  mul_smul x y τ := Subtype.ext (extConj_mul R K x.2 y.2 τ.1)

end Frattini

section Main

variable {Z : Subgroup H} {χ : H → ℂ} {θ : Z → ℂ} {e : ℕ}

theorem exists_constituent {G : Type*} [Group G] [Fintype G] {f : G → ℂ} (hf : IsNatComb f)
    (h1 : f 1 ≠ 0) : ∃ ψ ∈ Irr G, mult f ψ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h1
  rw [hf.eq_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun ψ hψ => by rw [hc ψ (mem_irrFinset.mp hψ)]; simp

/-- **Gagola, Lemma 2.3 (a) and (c).** -/
theorem lemma_2_3 [Z.Normal] (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) (K : Subgroup H) [hK : K.Normal] (hZK : Z ≤ K)
    (R : Subgroup H) (hZR : Z ≤ R) {p k : ℕ} (hp : p.Prime) (hRZ : Nat.card R = p ^ k * Nat.card Z)
    (hpR : ¬ p ∣ R.index) (hFrat : (NN R K) ⊔ K = ⊤)
    (hKcop : ¬ p ∣ Nat.card K / Nat.card (R ⊓ K : Subgroup H)) :
    ∃ σ ∈ Irr (K.subgroupOf R), ∃ b s : ℕ, 0 < b ∧
      b ^ 2 * s * Nat.card (K.subgroupOf R) = Nat.card R ∧
      (∃ hσ : σ ∈ Irr (K.subgroupOf R), (inertia (N := K.subgroupOf R) σ).index = s ∧
        ∃ φ ∈ Irr (inertia (N := K.subgroupOf R) σ), pull (inclI hσ) φ = (b : ℂ) • σ) ∧
      ∃ T : Subgroup H, K ≤ T ∧ T.index = s := by
  obtain ⟨ζ, hζ, a, hχR, ha⟩ := fr_sylow hχ hθ hres he hZR hp hRZ hpR
  set L := K.subgroupOf R
  -- a constituent `σ` of `ζ_L`
  have hζL := (irr_isNatComb hζ).pull L.subtype
  have hζ1 : pull L.subtype ζ 1 ≠ 0 := by
    obtain ⟨d, hd, hd'⟩ := irr_one hζ
    simp only [pull_apply, map_one, hd']
    exact_mod_cast hd.ne'
  obtain ⟨σ, hσ, hb⟩ := exists_constituent hζL hζ1
  set b := mult (pull L.subtype ζ) σ with hb_def
  set s := (orbitF (A := R) σ).card with hs_def
  have h3 : pull (R.subtype.comp L.subtype) χ = (a : ℂ) • pull L.subtype ζ := by
    funext l
    have := congrFun hχR (L.subtype l)
    simpa using this
  have hA : b ^ 2 * s * Nat.card L = Nat.card R := by
    have h1 := ip_res_self hζ hσ hb
    have h2 := fr_ip_pull hχ hθ hres he (φ := R.subtype.comp L.subtype)
      ((Subgroup.subtype_injective R).comp (Subgroup.subtype_injective L)) (by
        intro z hz
        exact ⟨⟨⟨z, hZR hz⟩, Subgroup.mem_subgroupOf.mpr (hZK hz)⟩, rfl⟩)
    rw [h3, ip_smul_left, ip_smul_right, h1] at h2
    have hHR : Nat.card H = R.index * Nat.card R := by rw [mul_comm, Subgroup.card_mul_index]
    rw [hHR, ← ha] at h2
    have ha0 : (a : ℂ) ≠ 0 := by
      intro h0
      have : a = 0 := by exact_mod_cast h0
      rw [this] at ha
      exact R.index_ne_zero_of_finite (by rw [← ha]; rfl)
    have h4 : ((a : ℂ) ^ 2) * (((b ^ 2 * s * Nat.card L : ℕ) : ℂ)) = (a : ℂ) ^ 2 * Nat.card R := by
      push_cast at h2 ⊢; linear_combination h2
    have h5 := mul_left_cancel₀ (pow_ne_zero 2 ha0) h4
    exact_mod_cast h5
  have hcardL : Nat.card L = Nat.card (R ⊓ K : Subgroup H) := by
    rw [show L = (R ⊓ K).subgroupOf R from (Subgroup.inf_subgroupOf_left K R).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  refine ⟨σ, hσ, b, s, Nat.pos_of_ne_zero hb, hA, ⟨hσ, index_inertia σ, ?_⟩, ?_⟩
  · -- (a): the character of the inertia group
    obtain ⟨φ, hφ, hφN, -⟩ := clifford_corr hζ hσ hb
    exact ⟨φ, hφ, hφN⟩
  · -- (c)
    have hχclass := irr_isClassFn hχ
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0] at ha; exact R.index_ne_zero_of_finite (by rw [← ha]; rfl)
    -- `Ω` is the set of constituents of `χ_L`
    have hmultχL : ∀ τ ∈ Irr L, mult (pull (R.subtype.comp L.subtype) χ) τ =
        a * mult (pull L.subtype ζ) τ := by
      intro τ hτ
      rw [h3]; exact mult_nsmul hζL a hτ
    have hΩchar : ∀ τ, τ ∈ orbitF (A := R) σ ↔
        τ ∈ Irr L ∧ mult (pull (R.subtype.comp L.subtype) χ) τ ≠ 0 := by
      intro τ
      constructor
      · intro hτ
        have hτI := orbitF_subset_irr hσ τ hτ
        refine ⟨hτI, ?_⟩
        rw [hmultχL τ hτI, mult_res_eq hζ hσ hb hτ]
        exact Nat.mul_ne_zero ha0 hb
      · rintro ⟨hτI, hτ0⟩
        rw [hmultχL τ hτI] at hτ0
        have : mult (pull L.subtype ζ) τ ≠ 0 := fun h0 => hτ0 (by rw [h0, mul_zero])
        obtain ⟨x, rfl⟩ := clifford_conj hζ hσ hb hτI this
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hΩstab : ∀ x (hx : x ∈ (NN R K)), ∀ τ ∈ orbitF (A := R) σ,
        extConj R K hx τ ∈ orbitF (A := R) σ := by
      intro x hx τ hτ
      rw [hΩchar] at hτ ⊢
      exact ⟨extConj_mem_irr R K hx hτ.1, by rw [mult_extConj R K hχclass hx]; exact hτ.2⟩
    letI instΩ := omegaAction R K (orbitF (A := R) σ) hΩstab
    have smul_val : ∀ (x : NN R K) (τ : {τ // τ ∈ orbitF (A := R) σ}),
        (x • τ).1 = extConj R K x.2 τ.1 := fun _ _ => rfl
    have hσΩ : σ ∈ orbitF (A := R) σ := Finset.mem_image.mpr ⟨1, Finset.mem_univ _, conjN_one σ⟩
    set σ₀ : {τ // τ ∈ orbitF (A := R) σ} := ⟨σ, hσΩ⟩
    -- the action is transitive
    have htrans : MulAction.IsPretransitive (NN R K) {τ // τ ∈ orbitF (A := R) σ} := by
      refine ⟨fun τ τ' => ?_⟩
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp τ.2
      obtain ⟨x', -, hx'⟩ := Finset.mem_image.mp τ'.2
      have hmem : ((x' * x⁻¹ : R) : H) ∈ (NN R K) := le_normalizer_inf R K (x' * x⁻¹).2
      refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
      refine (smul_val _ _).trans ?_
      rw [extConj_eq_conjN R K (x' * x⁻¹).2, ← hx, ← hx', ← conjN_mul]
      congr 1; ext; simp
    -- the stabilizer of `σ` has index `s`
    set S' := MulAction.stabilizer (NN R K) σ₀
    have hS'index : S'.index = s := by
      rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_coe]
    -- `N ∩ K` fixes `σ`
    set U' := K.subgroupOf (NN R K)
    have hU'normal : U'.Normal := hK.subgroupOf (NN R K)
    have hUS : U' ≤ S' := by
      -- the `U'`-orbit of `σ₀` is a block, so its size divides `s`
      set O := MulAction.orbit U' σ₀
      have hblock := MulAction.IsBlock.orbit_of_normal (G := (NN R K)) (N := U') σ₀
      have hcount := hblock.ncard_block_mul_ncard_orbit_eq ⟨σ₀, MulAction.mem_orbit_self σ₀⟩
      rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcount
      have hOs : O.ncard ∣ s := ⟨_, hcount.symm⟩
      -- and it divides `|N ∩ K : R ∩ K|`
      have hOst := MulAction.index_stabilizer U' σ₀
      have hstab : (R ⊓ K).subgroupOf (NN R K) ⊓ U' ≤ (MulAction.stabilizer U' σ₀).map U'.subtype := by
        intro m hm
        have hm1 := (Subgroup.mem_inf.mp hm).1
        have hm2 := (Subgroup.mem_inf.mp hm).2
        refine ⟨⟨m, hm2⟩, ?_, rfl⟩
        show (⟨m, hm2⟩ : U') • σ₀ = σ₀
        apply Subtype.ext
        rw [Subgroup.smul_def]
        refine (smul_val _ _).trans ?_
        exact extConj_of_mem_inf R K (Subgroup.mem_subgroupOf.mp hm1) (irr_isClassFn hσ)
      -- cardinalities
      have hcardU : Nat.card U' = Nat.card ((NN R K) ⊓ K : Subgroup H) := by
        rw [show U' = ((NN R K) ⊓ K).subgroupOf (NN R K) from (Subgroup.inf_subgroupOf_left K (NN R K)).symm]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      have hdivK : Nat.card ((NN R K) ⊓ K : Subgroup H) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
      have hRKle : R ⊓ K ≤ (NN R K) ⊓ K := le_inf (inf_le_normalizer R K) inf_le_right
      have hdivRK : Nat.card (R ⊓ K : Subgroup H) ∣ Nat.card ((NN R K) ⊓ K : Subgroup H) :=
        Subgroup.card_dvd_of_le hRKle
      have hstabcard : Nat.card (R ⊓ K : Subgroup H) ∣ Nat.card (MulAction.stabilizer U' σ₀) := by
        have h1 : Nat.card (((R ⊓ K).subgroupOf (NN R K) ⊓ U' : Subgroup (NN R K))) =
            Nat.card (R ⊓ K : Subgroup H) := by
          have : (R ⊓ K).subgroupOf (NN R K) ⊓ U' = (R ⊓ K).subgroupOf (NN R K) := by
            apply le_antisymm inf_le_left
            intro m hm
            exact ⟨hm, (Subgroup.mem_subgroupOf.mp hm).2⟩
          rw [this]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_normalizer R K)).toEquiv
        have h2 := Subgroup.card_dvd_of_le hstab
        rw [h1, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h2
        exact h2
      have hO : O.ncard * Nat.card (MulAction.stabilizer U' σ₀) = Nat.card U' := by
        rw [← hOst, Subgroup.index_mul_card]
      -- `O.ncard` is prime to `p`
      have hOcop : ¬ p ∣ O.ncard := by
        intro hpO
        obtain ⟨j, hj⟩ := hstabcard
        obtain ⟨i, hi⟩ := hdivK
        apply hKcop
        have hRKpos : 0 < Nat.card (R ⊓ K : Subgroup H) := Nat.card_pos
        have hKeq : Nat.card K = Nat.card (R ⊓ K : Subgroup H) * (O.ncard * j * i) := by
          rw [hi, ← hcardU, ← hO, hj]; ring
        rw [hKeq, Nat.mul_div_cancel_left _ hRKpos]
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hpO _) _
      -- `s` is a power of `p`
      have hspow : ∃ j, s = p ^ j := by
        have hZL : Nat.card Z ∣ Nat.card (R ⊓ K : Subgroup H) :=
          Subgroup.card_dvd_of_le (le_inf hZR hZK)
        obtain ⟨m, hm⟩ := hZL
        have hsdvd : s ∣ p ^ k := by
          have hZpos : 0 < Nat.card Z := Nat.card_pos
          have h1 : p ^ k * Nat.card Z = (b ^ 2 * s * m) * Nat.card Z := by
            rw [← hRZ, ← hA, hcardL, hm]; ring
          have h2 := Nat.eq_of_mul_eq_mul_right hZpos h1
          exact ⟨b ^ 2 * m, by rw [h2]; ring⟩
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hsdvd
        exact ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hspow
      have hO1 : O.ncard = 1 := by
        rw [hj] at hOs
        obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).mp hOs
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · rw [hi', h0, pow_zero]
        · exfalso; apply hOcop; rw [hi']; exact dvd_pow_self p hpos.ne'
      intro u hu
      have hmem : (⟨u, hu⟩ : U') • σ₀ ∈ O := MulAction.mem_orbit σ₀ _
      have hσmem : σ₀ ∈ O := MulAction.mem_orbit_self σ₀
      have := (Set.ncard_eq_one.mp hO1)
      obtain ⟨y, hy⟩ := this
      have h1 : (⟨u, hu⟩ : U') • σ₀ = y := by rw [hy] at hmem; exact hmem
      have h2 : σ₀ = y := by rw [hy] at hσmem; exact hσmem
      show u • σ₀ = σ₀
      rw [← h2] at h1
      exact h1
    -- the subgroup `T`
    set f : (NN R K) →* H ⧸ K := (QuotientGroup.mk' K).comp (NN R K).subtype
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective K y
      have hmem : h ∈ (((NN R K) ⊔ K : Subgroup H) : Set H) := by rw [hFrat]; trivial
      rw [Subgroup.mul_normal] at hmem
      obtain ⟨n, hn, k', hk', rfl⟩ := hmem
      refine ⟨⟨n, hn⟩, ?_⟩
      simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa using K.inv_mem hk'
    have hker : f.ker ≤ S' := by
      intro x hx
      apply hUS
      rw [MonoidHom.mem_ker] at hx
      simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact hx
    refine ⟨(S'.map f).comap (QuotientGroup.mk' K), ?_, ?_⟩
    · intro x hx
      show QuotientGroup.mk' K x ∈ S'.map f
      have : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this]
      exact (S'.map f).one_mem
    · rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K),
        Subgroup.index_map_eq _ hfsurj hker, hS'index]

end Main

end

end CFSGOutside.Gagola
