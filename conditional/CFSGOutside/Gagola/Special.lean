import CFSGOutside.Gagola.RepFacts
import CFSGOutside.Gagola.Cyclic
import CFSGOutside.Gagola.Lemma23

/-!
# Special elements over an invariant character (Gagola 1974, §3)

Let `N ⊴ G` and `θ ∈ Irr N` be `G`-invariant. Gagola's §3 reduces to the case `N` central with `θ`
faithful (his Theorem 1.1). We do not formalize that reduction; instead the notions are set up for
any normal `N`, following Gagola's own definition through extensions.

For `g ∈ G` let `L_g = N ⟨g⟩` (`cycN N g`). As `L_g / N` is cyclic, `θ` extends to `L_g`
(`exists_ext`), and two extensions agree on `g N` up to a scalar (`ext_proportional_G`). An element `g`
is **special** if an (equivalently, every) extension `ψ` of `θ` to `L_g` is fixed by every `x` with
`[x, g] ∈ N`. Gagola's `⟨⟨x, g⟩⟩` is the scalar by which `ψ^x` differs from `ψ` on `g N`, so this is
his definition.

* `char_eq_zero_of_not_special`: **Lemma 3.3**, an irreducible character over `θ` vanishes at
  non-special elements.
* `specialFn`: for special `g`, the class function supported on the `G`-conjugates of `g N` and
  equal to `ψ` on `g N`; it lies in the span of `Irr (G | θ)` (`specialFn_mem_span`).
* `irr_over_eq_of_special_le`: if every special element lies in `N`, then `θ` lies under at most one
  irreducible character of `G` (the part of **Theorem 3.1** used in Corollary 3.6).
* `card_special_le`: pairwise non-fused special elements are at most `|Irr (G | θ)|` in number (the
  other inequality of Theorem 3.1).
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

section General

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [hN : N.Normal]

/-- `L_g = N ⟨g⟩`. -/
abbrev cycN (N : Subgroup G) (g : G) : Subgroup G := N ⊔ Subgroup.zpowers g

/-- The inclusion `N → L_g`. -/
abbrev inclN (N : Subgroup G) (g : G) : N →* cycN N g := Subgroup.inclusion le_sup_left

theorem mem_cycN_self (g : G) : g ∈ cycN N g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

/-- `g` as an element of `L_g`. -/
abbrev gen (g : G) : cycN N g := ⟨g, mem_cycN_self g⟩

/-- Extension by zero of a function on a subgroup. -/
def ext0 {L : Subgroup G} (ψ : L → ℂ) : G → ℂ := Function.extend L.subtype ψ 0

theorem ext0_apply {L : Subgroup G} (ψ : L → ℂ) (l : L) : ext0 ψ l = ψ l :=
  (Subgroup.subtype_injective L).extend_apply ψ 0 l

theorem ext0_of_mem {L : Subgroup G} (ψ : L → ℂ) {y : G} (hy : y ∈ L) : ext0 ψ y = ψ ⟨y, hy⟩ :=
  ext0_apply ψ ⟨y, hy⟩

/-- `θ` is `G`-invariant. -/
def IsInvariant (θ : N → ℂ) : Prop := ∀ x : G, conjN N x θ = θ

/-- `ψ ∈ Irr L_g` extends `θ`. -/
def IsExt (θ : N → ℂ) (g : G) (ψ : cycN N g → ℂ) : Prop :=
  ψ ∈ Irr (cycN N g) ∧ pull (inclN N g) ψ = θ

theorem mul_mem_cycN (g : G) (n : N) : g * (n : G) ∈ cycN N g :=
  Subgroup.mul_mem _ (mem_cycN_self g) (Subgroup.mem_sup_left n.2)

theorem pow_mul_mem_cycN (g : G) (k : ℕ) (n : N) : g ^ k * (n : G) ∈ cycN N g :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers g k))
    (Subgroup.mem_sup_left n.2)

/-- Every element of `L_g` is `g^k n` with `k : ℕ`, `n ∈ N`. -/
theorem exists_pow_mul_of_mem_cycN {g y : G} (hy : y ∈ cycN N g) :
    ∃ (k : ℕ) (n : N), y = g ^ k * (n : G) := by
  have hy' : y ∈ ((Subgroup.zpowers g ⊔ N : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, sup_comm]; exact hy
  rw [Subgroup.mul_normal] at hy'
  obtain ⟨a, ha, n, hn, rfl⟩ := hy'
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨(z % (orderOf g : ℤ)).toNat, ⟨n, hn⟩, ?_⟩
  congr 1
  have hpos : (0 : ℤ) < orderOf g := by exact_mod_cast orderOf_pos g
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]

theorem conj_mem_of_comm_mem {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) :
    ∃ n₀ : N, x⁻¹ * g * x = g * (n₀ : G) := by
  have h1 : x⁻¹ * (x * g * x⁻¹ * g⁻¹) * x ∈ N := by
    simpa using hN.conj_mem _ hx x⁻¹
  have h2 : g⁻¹ * (x⁻¹ * (x * g * x⁻¹ * g⁻¹) * x)⁻¹ * g ∈ N := by
    simpa using hN.conj_mem _ (N.inv_mem h1) g⁻¹
  refine ⟨⟨_, h2⟩, ?_⟩
  simp only
  group

/-- If `[x, g] ∈ N` then conjugation by `x` keeps `g^k N` (and so `L_g`). -/
theorem conj_pow_mul {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) (k : ℕ) (n : N) :
    ∃ n' : N, x⁻¹ * (g ^ k * (n : G)) * x = g ^ k * (n' : G) := by
  obtain ⟨n₀, hn₀⟩ := conj_mem_of_comm_mem hx
  induction k generalizing n with
  | zero =>
    refine ⟨⟨x⁻¹ * n * x, conj_inv_mem N x n⟩, ?_⟩
    simp [mul_assoc]
  | succ k ih =>
    -- `x⁻¹ g^(k+1) n x = (x⁻¹ g x) (x⁻¹ g^k n x)`
    obtain ⟨n₁, hn₁⟩ := ih n
    have e : x⁻¹ * (g ^ (k + 1) * (n : G)) * x = (x⁻¹ * g * x) * (x⁻¹ * (g ^ k * n) * x) := by
      rw [pow_succ']; group
    rw [e, hn₀, hn₁]
    -- `g n₀ g^k n₁ = g^(k+1) (g^(-k) n₀ g^k) n₁`
    have hmem : (g ^ k)⁻¹ * (n₀ : G) * g ^ k ∈ N := conj_inv_mem N (g ^ k) n₀
    refine ⟨⟨(g ^ k)⁻¹ * n₀ * g ^ k, hmem⟩ * n₁, ?_⟩
    simp only [Subgroup.coe_mul]
    rw [pow_succ']; group

theorem conj_mem_cycN {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) {y : G} (hy : y ∈ cycN N g) :
    x⁻¹ * y * x ∈ cycN N g := by
  obtain ⟨k, n, rfl⟩ := exists_pow_mul_of_mem_cycN hy
  obtain ⟨n', hn'⟩ := conj_pow_mul hx k n
  rw [hn']
  exact pow_mul_mem_cycN g k n'

section Extension

variable {θ : N → ℂ}

/-- Conjugation by `g` on `N`, as an endomorphism. -/
def conjByN (N : Subgroup G) [N.Normal] (g : G) : N →* N where
  toFun n := ⟨g⁻¹ * n * g, conj_inv_mem N g n⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

/-- A natural combination containing `θ` and of degree `θ(1)` is `θ`. -/
theorem natComb_eq_of_mult_of_one {M : Type*} [Group M] [Fintype M] {f θ : M → ℂ} (hf : IsNatComb f)
    (hθ : θ ∈ Irr M) (hm : mult f θ ≠ 0) (h1 : f 1 = θ 1) : f = θ := by
  have hle : CharLE θ f := charLE_of_mult_pos hf hθ (Nat.one_le_iff_ne_zero.mpr hm)
  obtain ⟨d, hd, hd0⟩ := hle.one_eq
  have : d = 0 := by
    have : (f - θ) 1 = 0 := by simp [h1]
    rw [hd] at this; exact_mod_cast this
  have := hd0 this
  exact (sub_eq_zero.mp this)

/-- **`θ` extends to `L_g`.** -/
theorem exists_ext (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) (g : G) :
    ∃ ψ, IsExt θ g ψ := by
  set A := cycN N g
  set ι := inclN N g
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  -- a constituent of `θ^A`
  have hind : IsNatComb (indHom ι θ) := (irr_isNatComb hθ).indHom hι
  have hind1 : indHom ι θ 1 ≠ 0 := by
    have hval : ∀ x : A, Function.extend ι θ 0 (x * 1 * x⁻¹) = θ 1 := by
      intro x
      rw [mul_one, mul_inv_cancel, ← map_one ι, hι.extend_apply]
    simp only [indHom]
    rw [Finset.sum_congr rfl fun x _ => hval x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    obtain ⟨d, hd, hd'⟩ := irr_one hθ
    rw [hd']
    have h1 : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h2 : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    have h3 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    exact mul_ne_zero (inv_ne_zero h1) (mul_ne_zero h2 h3)
  obtain ⟨ψ, hψ, hm⟩ := exists_constituent hind hind1
  have hm' : mult (pull ι ψ) θ ≠ 0 := by
    have h1 := hind.mult_eq hψ
    rw [ip_indHom hι θ (irr_isClassFn hψ), ip_comm, ← ((irr_isNatComb hψ).pull ι).mult_eq hθ] at h1
    intro h0; apply hm
    have : (mult (indHom ι θ) ψ : ℂ) = 0 := by rw [h1, h0]; simp
    exact_mod_cast this
  have hgen : ∀ x : A, ∃ (l : N) (k : ℕ), x = ι l * (gen (N := N) g) ^ k := by
    intro x
    obtain ⟨k, n, hk⟩ := exists_pow_mul_of_mem_cycN x.2
    refine ⟨⟨g ^ k * n * (g ^ k)⁻¹, hN.conj_mem n n.2 (g ^ k)⟩, k, ?_⟩
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, SubgroupClass.coe_pow, ι]
    rw [hk]; group
  have hdeg := cyclic_res_eq ι (conjByN N g) (gen (N := N) g) (fun l => rfl) hgen hθ
    (fun l => congrFun (hinv g) l) hψ hm'
  refine ⟨ψ, hψ, natComb_eq_of_mult_of_one ((irr_isNatComb hψ).pull ι) hθ hm' ?_⟩
  simpa [pull_apply] using hdeg

/-- Two extensions of `θ` to `L_g` agree on each `g^k N` up to the scalar `z^k`. -/
theorem ext_proportional_G (hθ : θ ∈ Irr N) {g : G} {ψ ψ' : cycN N g → ℂ} (hψ : IsExt θ g ψ)
    (hψ' : IsExt θ g ψ') :
    ∃ z : ℂ, ∀ (k : ℕ) (n : N), ext0 ψ' (g ^ k * n) = z ^ k * ext0 ψ (g ^ k * n) := by
  obtain ⟨z, hz⟩ := ext_proportional (inclN N g) (conjByN N g) (gen (N := N) g) (fun l => rfl) hθ
    hψ.1 hψ'.1 hψ.2 hψ'.2
  refine ⟨z, fun k n => ?_⟩
  have he : (⟨g ^ k * n, pow_mul_mem_cycN g k n⟩ : cycN N g) = gen (N := N) g ^ k * inclN N g n := by
    ext; simp
  rw [ext0_of_mem _ (pow_mul_mem_cycN g k n), ext0_of_mem _ (pow_mul_mem_cycN g k n), he]
  exact hz k n

/-- Clifford's theorem for an invariant `θ`: `χ_N = ⟨χ_N, θ⟩ θ`. -/
theorem res_eq_mult_smul (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (hover : mult (pull N.subtype χ) θ ≠ 0) :
    pull N.subtype χ = (mult (pull N.subtype χ) θ : ℂ) • θ := by
  conv_lhs => rw [clifford_res hχ hθ hover]
  have : orbitF (A := G) θ = {θ} := by
    ext τ
    simp only [orbitF, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨x, rfl⟩; exact hinv x
    · rintro rfl; exact ⟨1, hinv 1⟩
  rw [this, Finset.sum_singleton]

/-- `χ(1) = ⟨χ_N, θ⟩ θ(1)` for `χ` over an invariant `θ`. -/
theorem one_eq_mult_mul (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (hover : mult (pull N.subtype χ) θ ≠ 0) :
    χ 1 = mult (pull N.subtype χ) θ * θ 1 := by
  have := congrFun (res_eq_mult_smul hθ hinv hχ hover) 1
  simpa using this

/-- The constituents of `χ_{L_g}`, for `χ` over an invariant `θ`, are extensions of `θ`. -/
theorem isExt_of_constituent (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (hover : mult (pull N.subtype χ) θ ≠ 0) (g : G) {ψ : cycN N g → ℂ}
    (hψ : ψ ∈ Irr (cycN N g)) (hm : mult (pull (cycN N g).subtype χ) ψ ≠ 0) : IsExt θ g ψ := by
  set ι := inclN N g
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  have hχA := (irr_isNatComb hχ).pull (cycN N g).subtype
  have hle : CharLE ψ (pull (cycN N g).subtype χ) := charLE_of_mult_pos hχA hψ (Nat.one_le_iff_ne_zero.mpr hm)
  have hle' := hle.pull ι
  have hres : pull ι (pull (cycN N g).subtype χ) = pull N.subtype χ := rfl
  rw [hres] at hle'
  have hψN := (irr_isNatComb hψ).pull ι
  -- every constituent of `ψ_N` is `θ`
  have honly : ∀ τ ∈ Irr N, τ ≠ θ → mult (pull ι ψ) τ = 0 := by
    intro τ hτ hne
    have h1 := hle'.mult_le hψN hτ
    have h2 : mult (pull N.subtype χ) τ = 0 := by
      have hip : ip (pull N.subtype χ) τ = 0 := by
        rw [res_eq_mult_smul hθ hinv hχ hover, ip_smul_left, ip_irr hθ hτ, if_neg (Ne.symm hne),
          mul_zero]
      have := ((irr_isNatComb hχ).pull N.subtype).mult_eq hτ
      rw [hip] at this
      exact_mod_cast this
    omega
  have hm' : mult (pull ι ψ) θ ≠ 0 := by
    intro h0
    have hz : pull ι ψ = 0 := by
      rw [hψN.eq_sum]
      refine Finset.sum_eq_zero fun τ hτ => ?_
      by_cases he : τ = θ
      · rw [he, h0]; simp
      · rw [honly τ (mem_irrFinset.mp hτ) he]; simp
    have := congrFun hz 1
    simp only [pull_apply, map_one, Pi.zero_apply] at this
    obtain ⟨d, hd, hd'⟩ := irr_one hψ
    rw [hd'] at this
    exact hd.ne' (by exact_mod_cast this)
  have hgen : ∀ x : cycN N g, ∃ (l : N) (k : ℕ), x = ι l * (gen (N := N) g) ^ k := by
    intro x
    obtain ⟨k, n, hk⟩ := exists_pow_mul_of_mem_cycN x.2
    refine ⟨⟨g ^ k * n * (g ^ k)⁻¹, hN.conj_mem n n.2 (g ^ k)⟩, k, ?_⟩
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, SubgroupClass.coe_pow, ι]
    rw [hk]; group
  have hdeg := cyclic_res_eq ι (conjByN N g) (gen (N := N) g) (fun l => rfl) hgen hθ
    (fun l => congrFun (hinv g) l) hψ hm'
  refine ⟨hψ, natComb_eq_of_mult_of_one hψN hθ hm' ?_⟩
  simpa [pull_apply] using hdeg

/-- **On `g N`, an irreducible character over `θ` is a multiple of an extension of `θ` to `L_g`.** -/
theorem coset_prop (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ} (hχ : χ ∈ Irr G)
    (hover : mult (pull N.subtype χ) θ ≠ 0) {g : G} {ψ : cycN N g → ℂ} (hψ : IsExt θ g ψ) :
    ∃ C : ℂ, ∀ n : N, χ (g * n) = C * ext0 ψ (g * n) := by
  have hχA := (irr_isNatComb hχ).pull (cycN N g).subtype
  have hz : ∀ ψ' ∈ irrFinset (cycN N g), ∃ z : ℂ, ∀ n : N,
      (mult (pull (cycN N g).subtype χ) ψ' : ℂ) * ψ' ⟨g * n, mul_mem_cycN g n⟩ =
        z * ext0 ψ (g * n) := by
    intro ψ' hψ'
    by_cases hm : mult (pull (cycN N g).subtype χ) ψ' = 0
    · exact ⟨0, fun n => by rw [hm]; simp⟩
    · have hext := isExt_of_constituent hθ hinv hχ hover g (mem_irrFinset.mp hψ') hm
      obtain ⟨z, hz⟩ := ext_proportional_G hθ hψ hext
      refine ⟨mult (pull (cycN N g).subtype χ) ψ' * z, fun n => ?_⟩
      have := hz 1 n
      simp only [pow_one] at this
      rw [ext0_of_mem _ (mul_mem_cycN g n)] at this
      rw [this]; ring
  choose zf hzf using hz
  refine ⟨∑ ψ' ∈ (irrFinset (cycN N g)).attach, zf ψ'.1 ψ'.2, fun n => ?_⟩
  have hmem : g * (n : G) ∈ cycN N g := mul_mem_cycN g n
  have h1 : χ (g * n) = pull (cycN N g).subtype χ ⟨g * n, hmem⟩ := rfl
  rw [h1, hχA.eq_sum, Finset.sum_apply, Finset.sum_mul, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun ψ' _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, hzf ψ'.1 ψ'.2 n]

theorem comm_mem_inv {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ ∈ N := by
  obtain ⟨n₀, hn₀⟩ := conj_mem_of_comm_mem hx
  rw [inv_inv, hn₀]
  simpa [mul_assoc] using hN.conj_mem n₀ n₀.2 g

/-- Conjugation `l ↦ x⁻¹ l x` of `L_g`, for `[x, g] ∈ N`. -/
def conjL {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) : cycN N g ≃* cycN N g where
  toFun l := ⟨x⁻¹ * l * x, conj_mem_cycN hx l.2⟩
  invFun l := ⟨x⁻¹⁻¹ * l * x⁻¹, conj_mem_cycN (comm_mem_inv hx) l.2⟩
  left_inv l := by ext; simp [mul_assoc]
  right_inv l := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem coe_conjL {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N) (l : cycN N g) :
    ((conjL hx l : cycN N g) : G) = x⁻¹ * l * x := rfl

/-- The conjugate `ψ^x` of an extension is an extension. -/
theorem isExt_conj (hinv : IsInvariant (G := G) θ) {x g : G} (hx : x * g * x⁻¹ * g⁻¹ ∈ N)
    {ψ : cycN N g → ℂ} (hψ : IsExt θ g ψ) : IsExt θ g (pull (conjL hx).toMonoidHom ψ) := by
  refine ⟨irr_pull_mulEquiv _ hψ.1, ?_⟩
  funext n
  have h1 := congrFun hψ.2 ⟨x⁻¹ * n * x, conj_inv_mem N x n⟩
  have h2 := congrFun (hinv x) n
  simp only [conjN_apply] at h2
  rw [← h2, ← h1]
  rfl

/-- **Special elements** (Gagola, §3): every extension `ψ` of `θ` to `L_g` is fixed by every `x`
with `[x, g] ∈ N`. -/
def IsSpecial (θ : N → ℂ) (g : G) : Prop :=
  ∀ ψ : cycN N g → ℂ, IsExt θ g ψ → ∀ x : G, x * g * x⁻¹ * g⁻¹ ∈ N →
    ∀ y ∈ cycN N g, ext0 ψ (x⁻¹ * y * x) = ext0 ψ y

/-- It is enough to check one extension. -/
theorem isSpecial_of_ext (hθ : θ ∈ Irr N) {g : G} {ψ : cycN N g → ℂ} (hψ : IsExt θ g ψ)
    (h : ∀ x : G, x * g * x⁻¹ * g⁻¹ ∈ N → ∀ y ∈ cycN N g, ext0 ψ (x⁻¹ * y * x) = ext0 ψ y) :
    IsSpecial θ g := by
  intro ψ' hψ' x hx y hy
  obtain ⟨z, hz⟩ := ext_proportional_G hθ hψ hψ'
  obtain ⟨k, n, rfl⟩ := exists_pow_mul_of_mem_cycN hy
  obtain ⟨n', hn'⟩ := conj_pow_mul hx k n
  rw [hn', hz, hz, ← hn', h x hx _ (pow_mul_mem_cycN g k n)]

/-- **Gagola, Lemma 3.3**: an irreducible character of `G` over `θ` vanishes at every non-special
element. -/
theorem char_eq_zero_of_not_special (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (hover : mult (pull N.subtype χ) θ ≠ 0) {g : G} (hg : ¬ IsSpecial θ g) :
    χ g = 0 := by
  simp only [IsSpecial, not_forall] at hg
  obtain ⟨ψ, hψ, x, hx, y, hy, hne⟩ := hg
  set ψx := pull (conjL hx).toMonoidHom ψ
  have hψx := isExt_conj hinv hx hψ
  obtain ⟨z, hz⟩ := ext_proportional_G hθ hψ hψx
  -- `z ≠ 1`, else `ψ^x = ψ`
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hne
    obtain ⟨k, n, rfl⟩ := exists_pow_mul_of_mem_cycN hy
    have := hz k n
    rw [one_pow, one_mul] at this
    rw [← this, ext0_of_mem _ (pow_mul_mem_cycN g k n), ext0_of_mem _ (conj_mem_cycN hx hy)]
    rfl
  obtain ⟨C, hC⟩ := coset_prop hθ hinv hχ hover hψ
  obtain ⟨n₀, hn₀⟩ := conj_mem_of_comm_mem hx
  have e1 : χ g = C * ext0 ψ g := by simpa using hC 1
  have e2 : χ g = χ (g * n₀) := by
    rw [← hn₀]; exact ((irr_isClassFn hχ).conj_eq g x).symm
  have e3 : ext0 ψ (g * n₀) = z * ext0 ψ g := by
    have := hz 1 1
    simp only [pow_one, OneMemClass.coe_one, mul_one] at this
    rw [← this, ext0_of_mem _ (mem_cycN_self g), ← hn₀, ext0_of_mem _ (conj_mem_cycN hx (mem_cycN_self g))]
    rfl
  rw [e2, hC n₀, e3] at e1
  have : C * ext0 ψ g * (z - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.mp this with h | h
  · rw [e2, hC n₀, e3]; linear_combination z * h
  · exact absurd (sub_eq_zero.mp h) hz1

end Extension

section SpecialFn

variable {θ : N → ℂ} {g : G} {ψ : cycN N g → ℂ}

theorem eq_mul_of_mul_inv_mem {g y : G} (h : y * g⁻¹ ∈ N) : ∃ n : N, y = g * n := by
  refine ⟨⟨g⁻¹ * (y * g⁻¹) * g, conj_inv_mem N g ⟨_, h⟩⟩, ?_⟩
  simp only; group

theorem mul_mem_cycN_of_mul_inv_mem {g y : G} (h : y * g⁻¹ ∈ N) : y ∈ cycN N g := by
  obtain ⟨n, rfl⟩ := eq_mul_of_mul_inv_mem h
  exact mul_mem_cycN g n

/-- If `w⁻¹ y₁ w = y₂` with `y₁, y₂ ∈ g N`, then `[w, g] ∈ N`. -/
theorem comm_mem_of_conj {w g y₁ y₂ : G} (h₁ : y₁ * g⁻¹ ∈ N) (h₂ : y₂ * g⁻¹ ∈ N)
    (h : w⁻¹ * y₁ * w = y₂) : w * g * w⁻¹ * g⁻¹ ∈ N := by
  obtain ⟨n₁, rfl⟩ := eq_mul_of_mul_inv_mem h₁
  obtain ⟨n₂, rfl⟩ := eq_mul_of_mul_inv_mem h₂
  -- `g⁻¹ w⁻¹ g w = n₂ (w⁻¹ n₁⁻¹ w)`
  have e1 : g⁻¹ * w⁻¹ * g * w ∈ N := by
    have : g⁻¹ * w⁻¹ * g * w = g⁻¹ * (w⁻¹ * (g * n₁) * w) * (w⁻¹ * (n₁ : G)⁻¹ * w) := by group
    rw [this, h, show g⁻¹ * (g * (n₂ : G)) * (w⁻¹ * (n₁ : G)⁻¹ * w) =
      (n₂ : G) * (w⁻¹ * (n₁ : G)⁻¹ * w) by group]
    exact N.mul_mem n₂.2 (conj_inv_mem N w n₁⁻¹)
  have e2 := hN.conj_mem _ (N.inv_mem e1) w
  have e3 := hN.conj_mem _ e2 g
  have : w * g * w⁻¹ * g⁻¹ = g * (w * (g⁻¹ * w⁻¹ * g * w)⁻¹ * w⁻¹) * g⁻¹ := by group
  rw [this]; exact e3

/-- The class function attached to a special element `g` and an extension `ψ` of `θ` to `L_g`:
`ψ` on `g N`, transported to the `G`-conjugates of `g N`, and `0` elsewhere. -/
def specialFn (g : G) (ψ : cycN N g → ℂ) : G → ℂ := fun y =>
  if h : ∃ u : G, u⁻¹ * y * u * g⁻¹ ∈ N then
    ext0 ψ ((Classical.choose h)⁻¹ * y * Classical.choose h)
  else 0

theorem specialFn_wd (hsp : IsSpecial θ g) (hψ : IsExt θ g ψ) {u v y : G}
    (hu : u⁻¹ * y * u * g⁻¹ ∈ N) (hv : v⁻¹ * y * v * g⁻¹ ∈ N) :
    ext0 ψ (u⁻¹ * y * u) = ext0 ψ (v⁻¹ * y * v) := by
  have hw : (u⁻¹ * v)⁻¹ * (u⁻¹ * y * u) * (u⁻¹ * v) = v⁻¹ * y * v := by group
  have hc := comm_mem_of_conj hu hv hw
  have := hsp ψ hψ (u⁻¹ * v) hc _ (mul_mem_cycN_of_mul_inv_mem hu)
  rw [hw] at this
  exact this.symm

theorem specialFn_apply_of (hsp : IsSpecial θ g) (hψ : IsExt θ g ψ) {u y : G}
    (hu : u⁻¹ * y * u * g⁻¹ ∈ N) : specialFn g ψ y = ext0 ψ (u⁻¹ * y * u) := by
  have h : ∃ u : G, u⁻¹ * y * u * g⁻¹ ∈ N := ⟨u, hu⟩
  simp only [specialFn, dif_pos h]
  exact specialFn_wd hsp hψ (Classical.choose_spec h) hu

theorem specialFn_of_not {y : G}
    (h : ¬ ∃ u : G, u⁻¹ * y * u * g⁻¹ ∈ N) : specialFn g ψ y = 0 := by
  simp only [specialFn, dif_neg h]

theorem specialFn_mul (hsp : IsSpecial θ g) (hψ : IsExt θ g ψ) (n : N) :
    specialFn g ψ (g * n) = ext0 ψ (g * n) := by
  have hu : (1 : G)⁻¹ * (g * n) * 1 * g⁻¹ ∈ N := by
    simpa [mul_assoc] using hN.conj_mem n n.2 g
  rw [specialFn_apply_of hsp hψ hu]
  simp

theorem specialFn_isClassFn (hsp : IsSpecial θ g) (hψ : IsExt θ g ψ) :
    IsClassFn (specialFn g ψ) := by
  intro y h
  by_cases hy : ∃ u : G, u⁻¹ * y * u * g⁻¹ ∈ N
  · obtain ⟨u, hu⟩ := hy
    have hu' : (h * u)⁻¹ * (h * y * h⁻¹) * (h * u) * g⁻¹ ∈ N := by
      convert hu using 1; group
    rw [specialFn_apply_of hsp hψ hu, specialFn_apply_of hsp hψ hu']
    congr 1; group
  · rw [specialFn_of_not hy, specialFn_of_not]
    rintro ⟨u, hu⟩
    exact hy ⟨h⁻¹ * u, by convert hu using 1; group⟩

/-- The projection identity `θ(1) ∑ₙ θ(n⁻¹) F(n y) = |N| F(y)` for `F = specialFn g ψ`. -/
theorem specialFn_proj (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) (hsp : IsSpecial θ g)
    (hψ : IsExt θ g ψ) (y : G) :
    θ 1 * ∑ n : N, θ n⁻¹ * specialFn g ψ (n * y) = Nat.card N * specialFn g ψ y := by
  by_cases hy : ∃ u : G, u⁻¹ * y * u * g⁻¹ ∈ N
  · obtain ⟨u, hu⟩ := hy
    have hl : u⁻¹ * y * u ∈ cycN N g := mul_mem_cycN_of_mul_inv_mem hu
    have hmem : ∀ n : N, u⁻¹ * (n * y) * u * g⁻¹ ∈ N := by
      intro n
      have : u⁻¹ * (n * y) * u * g⁻¹ = (u⁻¹ * n * u) * (u⁻¹ * y * u * g⁻¹) := by group
      rw [this]; exact N.mul_mem (conj_inv_mem N u n) hu
    have hterm : ∀ n : N, specialFn g ψ (n * y) =
        ψ (inclN N g ⟨u⁻¹ * n * u, conj_inv_mem N u n⟩ * ⟨u⁻¹ * y * u, hl⟩) := by
      intro n
      rw [specialFn_apply_of hsp hψ (hmem n), ext0_of_mem _ (by
        have : u⁻¹ * (n * y) * u = (u⁻¹ * n * u) * (u⁻¹ * y * u) := by group
        rw [this]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (conj_inv_mem N u n)) hl)]
      congr 1; ext; simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]; group
    rw [specialFn_apply_of hsp hψ hu, ext0_of_mem _ hl, Finset.sum_congr rfl fun n _ => by
      rw [hterm n], ← ext_sum (inclN N g) hθ hψ.1 hψ.2]
    congr 1
    -- reindex by `n ↦ u⁻¹ n u`
    let e : N ≃ N :=
      { toFun := fun n => ⟨u⁻¹ * n * u, conj_inv_mem N u n⟩
        invFun := fun n => ⟨u * n * u⁻¹, hN.conj_mem n n.2 u⟩
        left_inv := fun n => by ext; simp [mul_assoc]
        right_inv := fun n => by ext; simp [mul_assoc] }
    refine Fintype.sum_equiv e _ _ (fun n => ?_)
    congr 1
    have := congrFun (hinv u) n⁻¹
    simp only [conjN_apply] at this
    rw [← this]
    congr 1; ext; simp [e, mul_assoc]
  · rw [specialFn_of_not hy, mul_zero]
    have : ∀ n : N, specialFn g ψ (n * y) = 0 := by
      intro n
      apply specialFn_of_not
      rintro ⟨u, hu⟩
      apply hy
      refine ⟨u, ?_⟩
      have : u⁻¹ * y * u * g⁻¹ = (u⁻¹ * (n : G)⁻¹ * u) * (u⁻¹ * (n * y) * u * g⁻¹) := by group
      rw [this]; exact N.mul_mem (conj_inv_mem N u n⁻¹) hu
    simp [this]

/-- The operator `f ↦ θ(1) ∑ₙ θ(n⁻¹) f(n ·)`. -/
def projθ (θ : N → ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f y := θ 1 * ∑ n : N, θ n⁻¹ * f (n * y)
  map_add' f f' := by funext y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring

theorem projθ_irr (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    projθ θ χ = if mult (pull N.subtype χ) θ ≠ 0 then (Nat.card N : ℂ) • χ else 0 := by
  funext y
  have key := sum_mul_char_of_normal hinv hχ y
  have hm := ((irr_isNatComb hχ).pull N.subtype).mult_eq hθ
  rw [← hm] at key
  show θ 1 * _ = _
  split_ifs with hover
  · rw [one_eq_mult_mul hθ hinv hχ hover] at key
    have hm0 : (mult (pull N.subtype χ) θ : ℂ) ≠ 0 := by exact_mod_cast hover
    rw [Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hm0
    linear_combination key
  · push Not at hover
    rw [hover, Nat.cast_zero, mul_zero, zero_mul] at key
    obtain ⟨d, hd, hd'⟩ := irr_one hχ
    rw [hd'] at key
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have := (mul_eq_zero.mp key).resolve_left hd0
    simp [this]

/-- The span of the irreducible characters over `θ`. -/
abbrev spanOver (θ : N → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (((irrFinset G).filter fun χ => mult (pull N.subtype χ) θ ≠ 0 : Finset _) :
    Set (G → ℂ))

/-- A class function fixed (up to `|N|`) by the projection lies in the span of `Irr (G | θ)`. -/
theorem mem_spanOver (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {f : G → ℂ}
    (hf : IsClassFn f) (hP : projθ θ f = (Nat.card N : ℂ) • f) : f ∈ spanOver (G := G) θ := by
  have hN0 : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum := classFn_eq_sum hf
  have h2 : projθ θ f = (Nat.card N : ℂ) • ∑ χ ∈ (irrFinset G).filter
      (fun χ => mult (pull N.subtype χ) θ ≠ 0), ip f χ • χ := by
    conv_lhs => rw [hsum]
    rw [map_sum, Finset.smul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [map_smul, projθ_irr hθ hinv (mem_irrFinset.mp hχ)]
    split_ifs with h
    · rw [smul_comm]
    · rw [smul_zero]
  rw [hP] at h2
  have := smul_right_injective (G → ℂ) hN0 h2
  rw [this]
  refine Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ (Submodule.subset_span hχ)

theorem specialFn_mem_spanOver (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ)
    (hsp : IsSpecial θ g) (hψ : IsExt θ g ψ) : specialFn g ψ ∈ spanOver (G := G) θ :=
  mem_spanOver hθ hinv (specialFn_isClassFn hsp hψ) (by
    funext y
    rw [Pi.smul_apply, smul_eq_mul]
    exact specialFn_proj hθ hinv hsp hψ y)

end SpecialFn

end General

end

end CFSGOutside.Gagola
