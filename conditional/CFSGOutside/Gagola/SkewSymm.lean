import CFSGOutside.Gagola.Special

/-!
# A symmetry of special elements

Gagola uses that his pairing `⟨⟨x, y⟩⟩` is skew-symmetric; for `N` central this is immediate. Here we
prove the consequence needed in Lemma 4.4 for an arbitrary invariant `θ`: if `g` is special and
`g N` is central in `G/N`, then every `x ∈ G` has an extension of `θ` to `N ⟨x⟩` fixed by `g`
(`exists_ext_fixed`). With an explicit description of the elements commuting with `x` modulo `N`,
this makes `x` special (`isSpecial_of_explicit`).
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

section Irr

variable {L M : Type*} [Group L] [Fintype L] [Group M] [Fintype M]

/-- A nonzero natural combination below an irreducible character is that character. -/
theorem charLE_irr_eq {g θ : M → ℂ} (hg : IsNatComb g) (hθ : θ ∈ Irr M) (hle : CharLE g θ)
    (hg0 : g ≠ 0) : g = θ := by
  have hθn := irr_isNatComb hθ
  have hmle : ∀ ψ ∈ Irr M, mult g ψ ≤ if θ = ψ then 1 else 0 := by
    intro ψ hψ; rw [← irr_mult hθ hψ]; exact hle.mult_le hg hψ
  obtain ⟨ψ, hψ, hψ0⟩ : ∃ ψ ∈ Irr M, mult g ψ ≠ 0 := by
    by_contra hc; push Not at hc
    apply hg0
    rw [hg.eq_sum]
    exact Finset.sum_eq_zero fun ψ hψ => by rw [hc ψ (mem_irrFinset.mp hψ)]; simp
  have hψθ : θ = ψ := by
    by_contra hne; have := hmle ψ hψ; rw [if_neg hne] at this; omega
  subst hψθ
  rw [hg.eq_sum, Finset.sum_eq_single θ]
  · have := hmle θ hψ; rw [if_pos rfl] at this
    have h1 : mult g θ = 1 := by omega
    rw [h1]; simp
  · intro ψ' hψ' hne
    have := hmle ψ' (mem_irrFinset.mp hψ'); rw [if_neg (Ne.symm hne)] at this
    rw [show mult g ψ' = 0 by omega]; simp
  · intro h; exact absurd (mem_irrFinset.mpr hψ) h

/-- A character whose restriction is irreducible is irreducible. -/
theorem irr_of_pull_irr (j : M →* L) {f : L → ℂ} (hf : IsNatComb f) (hθ : pull j f ∈ Irr M) :
    f ∈ Irr L := by
  have hθ1 : pull j f 1 ≠ 0 := by
    obtain ⟨d, hd, hd'⟩ := irr_one hθ; rw [hd']; exact_mod_cast hd.ne'
  have hf1 : f 1 ≠ 0 := by simpa [pull_apply] using hθ1
  -- every constituent has degree `f(1)`
  have hdeg : ∀ φ ∈ Irr L, mult f φ ≠ 0 → φ 1 = f 1 := by
    intro φ hφ hm
    have hle := (charLE_of_mult_pos hf hφ (Nat.one_le_iff_ne_zero.mpr hm)).pull j
    have hφ0 : pull j φ ≠ 0 := by
      intro h0
      have := congrFun h0 1
      simp only [pull_apply, map_one, Pi.zero_apply] at this
      obtain ⟨d, hd, hd'⟩ := irr_one hφ
      rw [hd'] at this; exact hd.ne' (by exact_mod_cast this)
    have := charLE_irr_eq ((irr_isNatComb hφ).pull j) hθ hle hφ0
    have h1 := congrFun this 1
    simpa [pull_apply] using h1
  -- the multiplicities sum to one
  have hsum : ∑ φ ∈ irrFinset L, mult f φ = 1 := by
    have h1 : f 1 = ((∑ φ ∈ irrFinset L, mult f φ : ℕ) : ℂ) * f 1 := by
      conv_lhs => rw [hf.eq_sum]
      rw [Finset.sum_apply, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun φ hφ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases hm : mult f φ = 0
      · rw [hm]; simp
      · rw [hdeg φ (mem_irrFinset.mp hφ) hm]
    have h2 : ((∑ φ ∈ irrFinset L, mult f φ : ℕ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hf1 (h1.symm.trans (one_mul (f 1)).symm)
      exact this
    exact_mod_cast h2
  refine irr_of_natComb hf ?_
  rw [ip_natComb_self hf]
  have hle1 : ∀ φ ∈ irrFinset L, mult f φ ≤ 1 := fun φ hφ =>
    hsum ▸ Finset.single_le_sum (f := fun φ => mult f φ) (fun _ _ => Nat.zero_le _) hφ
  have hsq : ∑ φ ∈ irrFinset L, mult f φ ^ 2 = ∑ φ ∈ irrFinset L, mult f φ :=
    Finset.sum_congr rfl fun φ hφ => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle1 φ hφ) with h | h <;> rw [h] <;> rfl
  rw [← Nat.cast_sum, hsq, hsum, Nat.cast_one]

end Irr

section Skew

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [hN : N.Normal] {θ : N → ℂ}

/-- **Skew-symmetry, in the form used in Lemma 4.4.** If `g` is special and `[d, g] ∈ N` for all
`d`, then `θ` has an extension to `N ⟨x⟩` fixed by `g`, for every `x`. -/
theorem exists_ext_fixed (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {g : G}
    (hsp : IsSpecial θ g) (hgc : ∀ d : G, d * g * d⁻¹ * g⁻¹ ∈ N) (x : G) :
    ∃ ψ, IsExt θ x ψ ∧ ∀ y ∈ cycN N x, ext0 ψ (g⁻¹ * y * g) = ext0 ψ y := by
  set Lg := cycN N g
  haveI hLg : Lg.Normal := ⟨fun y hy d => by
    have := conj_mem_cycN (hgc d⁻¹) hy
    simpa using this⟩
  obtain ⟨ψg, hψg⟩ := exists_ext hθ hinv g
  -- `ψ_g` is `G`-invariant
  have hψginv : IsInvariant (G := G) ψg := by
    intro d
    funext y
    simp only [conjN_apply]
    have := hsp ψg hψg d (hgc d) y y.2
    rw [ext0_of_mem _ (conj_mem_cycN (hgc d) y.2), ext0_of_mem _ y.2] at this
    exact this
  obtain ⟨Ψ, hΨ⟩ := exists_ext hψg.1 hψginv x
  have hle : cycN N x ≤ cycN Lg x :=
    sup_le (le_trans (le_sup_left : N ≤ Lg) le_sup_left) le_sup_right
  set ι : cycN N x →* cycN Lg x := Subgroup.inclusion hle
  refine ⟨pull ι Ψ, ⟨?_, ?_⟩, ?_⟩
  · refine irr_of_pull_irr (inclN N x) ((irr_isNatComb hΨ.1).pull ι) ?_
    have : pull (inclN N x) (pull ι Ψ) = θ := by
      funext n
      have h1 := congrFun hΨ.2 ⟨n, le_sup_left (a := N) n.2⟩
      have h2 := congrFun hψg.2 n
      simp only [pull_apply] at h1 h2 ⊢
      rw [← h2]
      exact h1
    rw [this]; exact hθ
  · funext n
    have h1 := congrFun hΨ.2 ⟨n, le_sup_left (a := N) n.2⟩
    have h2 := congrFun hψg.2 n
    simp only [pull_apply] at h1 h2 ⊢
    rw [← h2]
    exact h1
  · intro y hy
    have hgx : g * x * g⁻¹ * x⁻¹ ∈ N := by
      have := N.inv_mem (hgc x); simpa [mul_assoc] using this
    rw [ext0_of_mem _ (conj_mem_cycN hgx hy), ext0_of_mem _ hy]
    simp only [pull_apply]
    have hgL : g ∈ cycN Lg x := le_sup_left (a := Lg) (mem_cycN_self g)
    have := (irr_isClassFn hΨ.1).conj_eq (ι ⟨y, hy⟩) ⟨g, hgL⟩
    exact (congrArg Ψ (Subtype.ext rfl)).trans this

theorem conj_pow_mem_cycN {g x : G} (hgx : g * x * g⁻¹ * x⁻¹ ∈ N) {y : G} (hy : y ∈ cycN N x)
    (j : ℕ) : (g ^ j)⁻¹ * y * g ^ j ∈ cycN N x := by
  induction j with
  | zero => simpa using hy
  | succ j ihj =>
    have e' : (g ^ (j + 1))⁻¹ * y * g ^ (j + 1) = g⁻¹ * ((g ^ j)⁻¹ * y * g ^ j) * g := by
      rw [pow_succ]; group
    rw [e']; exact conj_mem_cycN hgx ihj

/-- Invariance of an extension under conjugation by powers of `g`. -/
theorem ext_fixed_pow {g x : G} (hgx : g * x * g⁻¹ * x⁻¹ ∈ N) {ψ : cycN N x → ℂ}
    (hfix : ∀ y ∈ cycN N x, ext0 ψ (g⁻¹ * y * g) = ext0 ψ y) (j : ℕ) :
    ∀ y ∈ cycN N x, ext0 ψ ((g ^ j)⁻¹ * y * g ^ j) = ext0 ψ y := by
  induction j with
  | zero => intro y _; simp
  | succ j ih =>
    intro y hy
    have e : (g ^ (j + 1))⁻¹ * y * g ^ (j + 1) = g⁻¹ * ((g ^ j)⁻¹ * y * g ^ j) * g := by
      rw [pow_succ]; group
    have hmem : (g ^ j)⁻¹ * y * g ^ j ∈ cycN N x := conj_pow_mem_cycN hgx hy j
    rw [e, hfix _ hmem, ih y hy]

/-- An element is special if an extension of `θ` to `N ⟨x⟩` is fixed by `g`, and every element
commuting with `x` modulo `N` has the form `x^i g^j n`. -/
theorem isSpecial_of_explicit (hθ : θ ∈ Irr N) {g x : G} {ψ : cycN N x → ℂ} (hψ : IsExt θ x ψ)
    (hfix : ∀ y ∈ cycN N x, ext0 ψ (g⁻¹ * y * g) = ext0 ψ y) (hgx : g * x * g⁻¹ * x⁻¹ ∈ N)
    (hform : ∀ d : G, d * x * d⁻¹ * x⁻¹ ∈ N → ∃ i j : ℕ, ∃ n : N, d = x ^ i * g ^ j * n) :
    IsSpecial θ x := by
  refine isSpecial_of_ext hθ hψ fun d hd y hy => ?_
  obtain ⟨i, j, n, rfl⟩ := hform d hd
  have hcl := irr_isClassFn hψ.1
  have hxi : x ^ i ∈ cycN N x := Subgroup.pow_mem _ (mem_cycN_self x) i
  have hnL : (n : G) ∈ cycN N x := le_sup_left (a := N) n.2
  set y₁ := (x ^ i)⁻¹ * y * x ^ i
  have hy₁ : y₁ ∈ cycN N x :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxi) hy) hxi
  set y₂ := (g ^ j)⁻¹ * y₁ * g ^ j
  have hy₂ : y₂ ∈ cycN N x := conj_pow_mem_cycN hgx hy₁ j
  have e : (x ^ i * g ^ j * n)⁻¹ * y * (x ^ i * g ^ j * n) = (n : G)⁻¹ * y₂ * n := by
    simp only [y₂, y₁]; group
  have hmem3 : (n : G)⁻¹ * y₂ * n ∈ cycN N x :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnL) hy₂) hnL
  rw [e, ext0_of_mem _ hmem3, ext0_of_mem _ hy]
  have k1 : ψ ⟨(n : G)⁻¹ * y₂ * n, hmem3⟩ = ψ ⟨y₂, hy₂⟩ :=
    (congrArg ψ (Subtype.ext rfl)).trans (hcl.conj_eq ⟨y₂, hy₂⟩ ⟨n, hnL⟩)
  have k2 := ext_fixed_pow hgx hfix j y₁ hy₁
  rw [ext0_of_mem _ hy₂, ext0_of_mem _ hy₁] at k2
  have k3 : ψ ⟨y₁, hy₁⟩ = ψ ⟨y, hy⟩ :=
    (congrArg ψ (Subtype.ext rfl)).trans (hcl.conj_eq ⟨y, hy⟩ ⟨x ^ i, hxi⟩)
  rw [k1, k2, k3]

/-- If `g` is special with `g N` central in `G/N`, then so is every `g^i n`. -/
theorem isSpecial_of_central_power (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) {g : G}
    (hsp : IsSpecial θ g) (hgc : ∀ d : G, d * g * d⁻¹ * g⁻¹ ∈ N) (i : ℕ) (n : N) :
    IsSpecial θ (g ^ i * n) := by
  set x := g ^ i * (n : G)
  obtain ⟨ψg, hψg⟩ := exists_ext hθ hinv g
  have hψginv : ∀ d : G, ∀ y ∈ cycN N g, ext0 ψg (d⁻¹ * y * d) = ext0 ψg y :=
    fun d => hsp ψg hψg d (hgc d)
  have hle : cycN N x ≤ cycN N g := sup_le le_sup_left (by
    rw [Subgroup.zpowers_le]; exact pow_mul_mem_cycN g i n)
  set ι : cycN N x →* cycN N g := Subgroup.inclusion hle
  have hres : pull (inclN N x) (pull ι ψg) = θ := by
    funext m
    have := congrFun hψg.2 m
    simp only [pull_apply] at this ⊢
    exact this
  have hext : IsExt θ x (pull ι ψg) :=
    ⟨irr_of_pull_irr (inclN N x) ((irr_isNatComb hψg.1).pull ι) (by rw [hres]; exact hθ), hres⟩
  refine isSpecial_of_ext hθ hext fun d hd y hy => ?_
  have hy' : d⁻¹ * y * d ∈ cycN N x := conj_mem_cycN hd hy
  rw [ext0_of_mem _ hy', ext0_of_mem _ hy]
  simp only [pull_apply]
  have := hψginv d y (hle hy)
  rw [ext0_of_mem _ (hle hy'), ext0_of_mem _ (hle hy)] at this
  exact this

end Skew

end

end CFSGOutside.Gagola
