import CFSGOutside.HallOrthogonal.Irreducible

/-!
# Hall (2008), Theorem 1.1, orthogonal case: isotropic shears

An isotropic shear `σ` has `⟨σ x, x⟩ = 2 Q(x)`, so `(σ - 1) V` is totally isotropic and of dimension at least
two. In particular `dim V ≥ 4`. Hall's Lemma 3.6, in the form used here: if the reflection subgroup `R` is
irreducible, there is a root `a` of `R` with `σ a ≠ a`. Then the product of the reflections in `a` and `σ a`
is a nontrivial unipotent element, `u` with `(u - 1)³ = 0`. Over a field of characteristic `p ≥ 3` it has
order exactly `p`.
-/

namespace CFSGOutside.HallOrthogonal

open Module QuadraticMap
open CFSGOutside.Corpus.ClassicalGroups.Orthogonal (reflect)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Shear

variable {σ : V ≃ₗ[K] V}

theorem shear_sq_apply (hσ : ((σ : V →ₗ[K] V) - 1) ^ 2 = 0) (x : V) :
    σ (σ x) = (2 : K) • σ x - x := by
  have := congrArg (fun f : Module.End K V => f x) hσ
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, map_sub, LinearMap.zero_apply] at this
  rw [two_smul]
  linear_combination (norm := module) this

theorem polar_shear_self (h2 : (2 : K) ≠ 0) (hσO : σ ∈ orthGroup Q)
    (hσ : ((σ : V →ₗ[K] V) - 1) ^ 2 = 0) (x : V) : polar Q x (σ x) = 2 * Q x := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσO (σ x) x
  have h3 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hσO x
  rw [shear_sq_apply hσ, polar_sub_left, polar_smul_left, polar_self_eq, h3, smul_eq_mul] at h1
  rw [polar_comm Q x (σ x)] at h1
  rw [polar_comm]
  have : (2 : K) * polar Q (σ x) x = 2 * (2 * Q x) := by linear_combination (-1 : K) * h1
  exact mul_left_cancel₀ h2 this

theorem map_shear_sub (h2 : (2 : K) ≠ 0) (hσO : σ ∈ orthGroup Q)
    (hσ : ((σ : V →ₗ[K] V) - 1) ^ 2 = 0) (x : V) : Q (σ x - x) = 0 := by
  have h3 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hσO x
  rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, polar_comm,
    polar_shear_self h2 hσO hσ, h3]
  ring

theorem polar_shear_sub (h2 : (2 : K) ≠ 0) (hσO : σ ∈ orthGroup Q)
    (hσ : ((σ : V →ₗ[K] V) - 1) ^ 2 = 0) (x y : V) : polar Q (σ x - x) (σ y - y) = 0 := by
  have h := map_shear_sub h2 hσO hσ (x + y)
  rw [show σ (x + y) - (x + y) = (σ x - x) + (σ y - y) by rw [map_add]; abel,
    QuadraticMap.map_add Q, map_shear_sub h2 hσO hσ x, map_shear_sub h2 hσO hσ y, zero_add,
    zero_add] at h
  exact h

/-- An isotropic shear lives in dimension at least `4`. -/
theorem four_le_finrank [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hσ : IsIsotropicShear Q σ) : 4 ≤ finrank K V := by
  obtain ⟨hσO, hσ1, -, hσ2⟩ := hσ
  set N : V →ₗ[K] V := (σ : V →ₗ[K] V) - 1
  set W := LinearMap.range N
  have hN : ∀ x, N x = σ x - x := fun x => rfl
  -- `W` is totally isotropic
  have hiso : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro _ ⟨y, rfl⟩
    change polarBilin Q (N y) (N x) = 0
    rw [polarBilin_apply_apply, hN, hN]
    exact polar_shear_sub h2 hσO hσ2 y x
  have hdim : 2 * finrank K W ≤ finrank K V := by
    have h1 := Submodule.finrank_mono hiso
    rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
    have : finrank K W ≤ finrank K V := Submodule.finrank_le W
    omega
  -- `dim W ≥ 2`: otherwise `σ` is an isometric transvection
  have hW2 : 2 ≤ finrank K W := by
    by_contra hlt
    push Not at hlt
    have hW0 : W ≠ ⊥ := by
      intro h
      apply hσ1
      refine LinearEquiv.ext fun x => ?_
      have : N x ∈ W := ⟨x, rfl⟩
      rw [h, Submodule.mem_bot, hN, sub_eq_zero] at this
      exact this
    have hW1 : finrank K W = 1 := by
      have := Submodule.finrank_eq_zero.not.2 hW0
      omega
    obtain ⟨w, φ, hw, hφ, hx⟩ := exists_rankOne (σ : V →ₗ[K] V) hW1
    replace hx : ∀ x, σ x = x + φ x • w := fun x => hx x
    have key : ∀ x y, φ y * polar Q x w + φ x * polar Q w y = 0 := by
      intro x y
      have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσO x y
      have hww : polar Q w w = 0 := by
        have h3 := map_shear_sub h2 hσO hσ2 x
        obtain ⟨z, hz⟩ : ∃ z, φ z ≠ 0 := by
          by_contra hc
          push Not at hc
          exact hφ (LinearMap.ext hc)
        have h4 := map_shear_sub h2 hσO hσ2 z
        rw [hx z, add_sub_cancel_left, QuadraticMap.map_smul, smul_eq_mul] at h4
        rw [polar_self_eq, (mul_eq_zero.mp h4).resolve_left (mul_ne_zero hz hz), mul_zero]
      rw [hx x, hx y, polar_add_left, polar_add_right, polar_add_right, polar_smul_left,
        polar_smul_right, polar_smul_left, polar_smul_right, hww] at h1
      simp only [smul_eq_mul] at h1
      linear_combination h1
    obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hφ (LinearMap.ext hc)
    obtain ⟨y0, hy0⟩ : ∃ y, polar Q w y ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw (hQ.1 w fun y => by rw [polarBilin_apply_apply]; exact hc y)
    have hself : ∀ x, φ x * polar Q x w = 0 := by
      intro x
      have := key x x
      rw [polar_comm Q w x] at this
      have : (2 : K) * (φ x * polar Q x w) = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    have hx0w : polar Q x0 w = 0 := (mul_eq_zero.mp (hself x0)).resolve_left hx0
    have hy0φ : φ y0 = 0 := by
      have := hself y0
      rw [polar_comm] at this
      exact (mul_eq_zero.mp this).resolve_right hy0
    have := hself (x0 + y0)
    rw [map_add, hy0φ, add_zero, polar_add_left, hx0w, zero_add, polar_comm] at this
    exact mul_ne_zero hx0 hy0 this
  omega

end Shear

/-- Powers of `1 + N` with `N³ = 0`. -/
theorem pow_of_cube_eq_zero {R : Type*} [Ring R] {N : R} (hN : N ^ 3 = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : R) * N + (n.choose 2 : R) * N ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    have h3 : N ^ 2 * N = 0 := by rw [← pow_succ]; exact hN
    have : (1 + (n : R) * N + (n.choose 2 : R) * N ^ 2) * (1 + N) =
        1 + ((n : R) + 1) * N + ((n : R) + (n.choose 2 : R)) * N ^ 2 +
          (n.choose 2 : R) * (N ^ 2 * N) := by
      simp only [add_mul, mul_add, mul_one, one_mul, pow_two, mul_assoc]
      abel
    rw [this, h3, mul_zero, add_zero]

section Lemma36

variable [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
include h2 hQ

/-- The span of the roots of the reflections in `H` is invariant under `H` when `H ≤ O(V)`. -/
theorem roots_span_top {H : Subgroup (V ≃ₗ[K] V)} (hHO : H ≤ orthGroup Q) (hirr : IsIrreducible H)
    {a₀ : V} (ha₀ : Q a₀ ≠ 0) (ha₀H : reflect Q a₀ ∈ H) :
    Submodule.span K {a | Q a ≠ 0 ∧ reflect Q a ∈ H} = ⊤ := by
  set Sp := Submodule.span K {a | Q a ≠ 0 ∧ reflect Q a ∈ H}
  have hinv : IsInvariant H Sp := by
    intro h hh x hx
    refine Submodule.span_induction (p := fun x _ => h x ∈ Sp) ?_ ?_ ?_ ?_ hx
    · rintro a ⟨ha, haH⟩
      refine Submodule.subset_span ⟨?_, ?_⟩
      · rwa [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hHO hh)]
      · rw [← reflect_conj (hHO hh)]
        exact H.mul_mem (H.mul_mem hh haH) (H.inv_mem hh)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact Sp.add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Sp.smul_mem c hx
  rcases hirr.2 Sp hinv with h | h
  · exfalso
    have : a₀ ∈ Sp := Submodule.subset_span ⟨ha₀, ha₀H⟩
    rw [h, Submodule.mem_bot] at this
    exact ha₀ (by rw [this, QuadraticMap.map_zero])
  · exact h

/-- **Hall, Lemma 3.6.** If `R` is irreducible and `G` contains an isotropic shear, then `R` contains
reflections `ρ = r_a`, `ρ' = r_b` whose product has order `p = char K`. -/
theorem exists_reflect_mul_orderOf {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp3 : 3 ≤ p)
    {G : Subgroup (V ≃ₗ[K] V)} (hGO : G ≤ orthGroup Q) (hRirr : IsIrreducible (reflGroup Q G))
    (hT : ∃ t, t ∈ reflSet Q G) {σ : V ≃ₗ[K] V} (hσG : σ ∈ G) (hσ : IsIsotropicShear Q σ) :
    ∃ a b : V, Q a ≠ 0 ∧ Q b ≠ 0 ∧ reflect Q a ∈ reflGroup Q G ∧ reflect Q b ∈ reflGroup Q G ∧
      orderOf (reflect Q a * reflect Q b) = p := by
  obtain ⟨hσO, hσ1, -, hσ2⟩ := hσ
  have hRO : reflGroup Q G ≤ orthGroup Q := reflGroup_le.trans hGO
  obtain ⟨t₀, ht₀⟩ := hT
  obtain ⟨a₀, ha₀, rfl⟩ := (isReflection_iff h2 hQ).1 ht₀.2
  have hspan := roots_span_top h2 hQ hRO hRirr ha₀ (Subgroup.subset_closure ht₀)
  -- a root moved by `σ`
  obtain ⟨a, ⟨ha, haR⟩, hσa⟩ : ∃ a ∈ {a | Q a ≠ 0 ∧ reflect Q a ∈ reflGroup Q G}, σ a ≠ a := by
    by_contra hc
    push Not at hc
    apply hσ1
    have hle : Submodule.span K {a | Q a ≠ 0 ∧ reflect Q a ∈ reflGroup Q G} ≤ fixSpace σ :=
      Submodule.span_le.2 fun a ha => by
        change (((σ : V →ₗ[K] V) - LinearMap.id : V →ₗ[K] V) a) = 0
        rw [LinearMap.sub_apply, LinearEquiv.coe_coe, hc a ha, LinearMap.id_apply, sub_self]
    rw [hspan, top_le_iff] at hle
    refine LinearEquiv.ext fun x => ?_
    have : x ∈ fixSpace σ := hle ▸ Submodule.mem_top
    change (((σ : V →ₗ[K] V) - LinearMap.id : V →ₗ[K] V) x) = 0 at this
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  set b := σ a with hb
  have hQb : Q b = Q a := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hσO a
  have hbR : reflect Q b ∈ reflGroup Q G := by
    rw [hb, ← reflect_conj hσO]
    exact conj_mem_reflGroup h2 hQ hGO hσG haR
  have hab : polar Q a b = 2 * Q a := polar_shear_self h2 hσO hσ2 a
  set q := Q a
  set w := b - a with hw
  have hw0 : w ≠ 0 := sub_ne_zero.2 hσa
  have haa : polar Q a a = 2 * q := polar_self_eq Q a
  have hbb : polar Q b b = 2 * q := by rw [polar_self_eq, hQb]
  have hba : polar Q b a = 2 * q := by rw [polar_comm, hab]
  refine ⟨a, b, ha, by rwa [hQb], haR, hbR, ?_⟩
  -- the nilpotent part `N = r_a r_b - 1`
  set u := reflect Q a * reflect Q b
  set N : Module.End K V := (u : V →ₗ[K] V) - 1
  have hNx : ∀ x, N x = -(polar Q b x / q) • b - ((polar Q a x - 2 * polar Q b x) / q) • a := by
    intro x
    change u x - x = _
    rw [LinearEquiv.mul_apply, reflect_apply Q (by rwa [hQb]) x, reflect_apply Q ha, hQb,
      polar_sub_right, polar_smul_right, hab, smul_eq_mul]
    have : polar Q a x - polar Q b x / q * (2 * q) = polar Q a x - 2 * polar Q b x := by
      field_simp
    rw [this]
    module
  have hpaN : ∀ x, polar Q a (N x) = 2 * (polar Q b x - polar Q a x) := by
    intro x
    rw [hNx, polar_sub_right, polar_smul_right, polar_smul_right, hab, haa, smul_eq_mul,
      smul_eq_mul]
    field_simp
    ring
  have hpbN : ∀ x, polar Q b (N x) = 2 * (polar Q b x - polar Q a x) := by
    intro x
    rw [hNx, polar_sub_right, polar_smul_right, polar_smul_right, hbb, hba, smul_eq_mul,
      smul_eq_mul]
    field_simp
    ring
  have hNN : ∀ x, N (N x) = -((2 * (polar Q b x - polar Q a x)) / q) • w := by
    intro x
    rw [hNx (N x), hpaN, hpbN, hw]
    have : (2 * (polar Q b x - polar Q a x) - 2 * (2 * (polar Q b x - polar Q a x))) / q =
        -((2 * (polar Q b x - polar Q a x)) / q) := by ring
    rw [this]
    module
  have hNw : N w = 0 := by
    rw [hNx, hw, polar_sub_right, polar_sub_right, hbb, hba, hab, haa]
    simp
  have hN3 : N ^ 3 = 0 := by
    ext x
    rw [pow_succ, pow_two, Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply, hNN,
      hpaN, hpbN, sub_self, mul_zero, zero_div, neg_zero, zero_smul]
  have hu : (u : V →ₗ[K] V) = 1 + N := by simp [N]
  have hcast : ∀ m : ℕ, (p : ℕ) ∣ m → ((m : ℕ) : Module.End K V) = 0 := by
    intro m hm
    rw [← map_natCast (algebraMap K (Module.End K V)), (CharP.cast_eq_zero_iff K p m).2 hm,
      map_zero]
  have hcoe : ∀ n : ℕ, ((u ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) = (u : V →ₗ[K] V) ^ n := fun n =>
    map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom u n
  have hup : u ^ p = 1 := by
    apply LinearEquiv.toLinearMap_injective
    rw [hcoe, hu, pow_of_cube_eq_zero hN3, hcast p dvd_rfl,
      hcast _ (hp.out.dvd_choose_self (by norm_num) (by omega)), zero_mul, zero_mul, add_zero,
      add_zero]
    rfl
  have hu1 : u ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ : ∃ v, polar Q w v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hw0 (hQ.1 w fun y => by rw [polarBilin_apply_apply]; exact hc y)
    have hN0 : N = 0 := by
      have h1' : ((u : V ≃ₗ[K] V) : V →ₗ[K] V) = 1 := by rw [h1]; ext; rfl
      simp only [N, h1', sub_self]
    have := hNN v
    rw [hN0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    rcases this with h | h
    · apply hv
      have hq : q ≠ 0 := ha
      rw [neg_eq_zero, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [hw, polar_sub_left]
        exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h hq
    · exact hw0 h
  exact orderOf_eq_prime hup hu1

end Lemma36

end CFSGOutside.HallOrthogonal
