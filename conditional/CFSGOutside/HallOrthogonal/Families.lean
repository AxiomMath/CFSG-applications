import CFSGOutside.HallOrthogonal.SpinorKernel
import CFSGOutside.HallOrthogonal.Irreducible

/-!
# Hall (2008), Theorem 1.1, orthogonal case: the Zalesskiĭ–Serežkin families

Let `A ≤ O(V)` be irreducible, contain a reflection, and contain two reflections whose product has order
`p ≥ 5`, with `dim V ≥ 4`. Going through the families of Zalesskiĭ–Serežkin:

* `slpm` contains transvections, which are not isometries;
* `gmmn` and `g2mmn` are impossible by Hall's Lemma 3.7;
* `exc` and `h4` have products of reflections of order at most `5`, and the rows with `5` are excluded;
* `orth` and `orthClass` are `O(V)` and `classClosure Q c`, since an invariant quadratic form of an
  absolutely irreducible group is a multiple of `Q`.

Only the Weyl family `weyl` is left; `CFSGOutside.HallOrthogonal.Weyl` rules it out.
-/

namespace CFSGOutside.HallOrthogonal

open Module QuadraticMap
open CFSGOutside.Corpus.ClassicalGroups.Orthogonal (reflect)
open CFSGOutside.Corpus.StandardType.ZS

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

section Schur

variable (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
include h2 hQ

/-- An invariant quadratic form of an irreducible group containing a reflection is a multiple of `Q`. -/
theorem exists_eq_smul_of_invariant {A : Subgroup (V ≃ₗ[K] V)} (hAO : A ≤ orthGroup Q)
    (hirr : IsIrreducible A) {a : V} (ha : Q a ≠ 0) (haA : reflect Q a ∈ A)
    {Q' : QuadraticForm K V} (hQ' : (polarBilin Q').Nondegenerate)
    (hA' : ∀ g ∈ A, ∀ v, Q' (g v) = Q' v) : ∃ c : K, c ≠ 0 ∧ ∀ v, Q' v = c * Q v := by
  set B := polarBilin Q
  set B' := polarBilin Q'
  let T : Module.End K V := (LinearMap.BilinForm.toDual B hQ).symm.toLinearMap ∘ₗ B'
  have hT : ∀ x y, B (T x) y = B' x y := by
    intro x y
    have := LinearMap.BilinForm.toDual_def hQ (m := T x) (n := y)
    rw [← this]
    simp [T]
  have hcomm : ∀ g ∈ A, T ∘ₗ (g : V →ₗ[K] V) = (g : V →ₗ[K] V) ∘ₗ T := by
    intro g hg
    ext x
    rw [← sub_eq_zero]
    apply hQ.1
    intro y
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hT]
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO hg) (T x) (g⁻¹ y)
    rw [apply_inv_apply] at h1
    change polar Q' (g x) y = polar Q (g (T x)) y
    rw [h1]
    have hg' : ∀ v, Q' (g v) = Q' v := hA' g hg
    have h3 : polar Q' (g x) (g (g⁻¹ y)) = polar Q' x (g⁻¹ y) := by
      simp only [polar, ← map_add, hg']
    rw [apply_inv_apply] at h3
    rw [h3]
    exact (hT x (g⁻¹ y)).symm
  obtain ⟨c, hc⟩ := commute_eq_scalar h2 hirr ha haA T hcomm
  have hpol : ∀ x y, polar Q' x y = c * polar Q x y := by
    intro x y
    have := hT x y
    rw [hc] at this
    simpa [B, B', polarBilin_apply_apply, polar_smul_left] using this.symm
  refine ⟨c, ?_, fun v => ?_⟩
  · rintro rfl
    have hv : a = 0 := hQ'.1 a fun y => by
      rw [polarBilin_apply_apply, hpol, zero_mul]
    exact ha (by rw [hv, QuadraticMap.map_zero])
  · have := hpol v v
    rw [polar_self_eq, polar_self_eq] at this
    have : (2 : K) * Q' v = 2 * (c * Q v) := by linear_combination this
    exact mul_left_cancel₀ h2 this

end Schur

section Transvection

variable (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
include h2 hQ

/-- A transvection `x ↦ x + φ x • v` is not an isometry. -/
theorem transvection_not_isometry {v : V} (hv : v ≠ 0) {φ : Dual K V} (hφ : φ ≠ 0)
    (hφv : φ v = 0) (hiso : ∀ x, Q (x + φ x • v) = Q x) : False := by
  obtain ⟨x0, hx0⟩ : ∃ x, φ x = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hc; push Not at hc; exact hφ (LinearMap.ext hc)
    exact ⟨(φ x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩
  have hexp : ∀ z, Q (z + v) = Q z + Q v + polar Q z v := fun z => QuadraticMap.map_add Q z v
  have hker : ∀ y, φ y = 0 → polar Q y v = 0 := by
    intro y hy
    have h1 := hiso (x0 + y)
    rw [show φ (x0 + y) = 1 by rw [map_add, hx0, hy, add_zero], one_smul, hexp] at h1
    have h0 := hiso x0
    rw [hx0, one_smul, hexp] at h0
    rw [polar_add_left] at h1
    linear_combination h1 - h0
  have hQv : Q v = 0 := by
    have := hker v hφv
    rw [polar_self_eq] at this
    exact (mul_eq_zero.mp this).resolve_left h2
  have hx0v : polar Q x0 v = 0 := by
    have h0 := hiso x0
    rw [hx0, one_smul, hexp, hQv] at h0
    linear_combination h0
  apply hv
  apply hQ.1 v
  intro z
  rw [polarBilin_apply_apply, polar_comm]
  have hz : z = (φ z) • x0 + (z - (φ z) • x0) := by abel
  rw [hz, polar_add_left, polar_smul_left, hx0v, smul_zero, zero_add]
  apply hker
  rw [map_sub, map_smul, hx0, smul_eq_mul, mul_one, sub_self]

end Transvection

section Families

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [FiniteDimensional (ZMod p) U] {Q : QuadraticForm (ZMod p) U}

theorem permMap_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : permMap p f σ (f i) = f (σ i) := by
  simp [permMap, Module.Basis.equiv_apply]

theorem diagMap_apply {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ)
    (i : Fin n) : diagMap p f d (f i) = ((d i : ZMod p)) • f i := by
  simp [diagMap, Module.Basis.equivFun_symm_apply, LinearEquiv.smulOfUnit, Finsupp.single_apply,
    Units.smul_def, ite_smul]

/-- **Hall, Lemma 3.7.** No monomial group `G(m, m, n)` or `G(2m, m, n)` with `m` large lies in `O(V)`:
the permutation matrices force `⟨f_i, f_j⟩ = a δ_ij + b (1 - δ_ij)` and the diagonal element forces
`a = b = 0`. -/
theorem monomial_false (hp2 : p ≠ 2) (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) (hn : 3 ≤ n) {i₀ i₁ : Fin n} (h01 : i₀ ≠ i₁)
    {ζ : (ZMod p)ˣ} (hζ : ζ ^ 2 ≠ 1) (hperm : ∀ σ, permMap p f σ ∈ orthGroup Q)
    (hdiag : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ orthGroup Q) : False := by
  classical
  set B : Fin n → Fin n → ZMod p := fun i j => polar Q (f i) (f j)
  have hB : ∀ σ : Equiv.Perm (Fin n), ∀ i j, B (σ i) (σ j) = B i j := by
    intro σ i j
    simp only [B, ← permMap_apply f σ]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hperm σ) _ _
  have hD : ∀ i j, (pairUnit p i₀ i₁ ζ i : ZMod p) * (pairUnit p i₀ i₁ ζ j : ZMod p) * B i j =
      B i j := by
    intro i j
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hdiag (f i) (f j)
    rw [diagMap_apply, diagMap_apply, polar_smul_left, polar_smul_right, smul_eq_mul,
      smul_eq_mul] at this
    simp only [B]
    linear_combination this
  -- a third index
  obtain ⟨k, hk0, hk1⟩ : ∃ k : Fin n, k ≠ i₀ ∧ k ≠ i₁ := by
    by_contra hc
    push Not at hc
    have : (Finset.univ : Finset (Fin n)) ⊆ {i₀, i₁} := fun x _ => by
      by_cases hx : x = i₀
      · simp [hx]
      · simp [hc x hx]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := this.trans (Finset.card_le_two)
    omega
  have hζ1 : (ζ : ZMod p) ≠ 1 := by
    intro h
    apply hζ
    have : ζ = 1 := Units.ext h
    rw [this, one_pow]
  have hζ2 : (ζ : ZMod p) ^ 2 ≠ 1 := by
    intro h
    apply hζ
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have hu0 : (pairUnit p i₀ i₁ ζ i₀ : ZMod p) = ζ := by simp [pairUnit]
  have huk : (pairUnit p i₀ i₁ ζ k : ZMod p) = 1 := by simp [pairUnit, hk0, hk1]
  have hoff : B i₀ k = 0 := by
    have := hD i₀ k
    rw [hu0, huk, mul_one] at this
    have : ((ζ : ZMod p) - 1) * B i₀ k = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.2 hζ1)
  have hdg : B i₀ i₀ = 0 := by
    have := hD i₀ i₀
    rw [hu0] at this
    have : ((ζ : ZMod p) ^ 2 - 1) * B i₀ i₀ = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.2 hζ2)
  -- every entry vanishes
  have hall : ∀ i j, B i j = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := hB (Equiv.swap i₀ i) i₀ i₀
      rw [Equiv.swap_apply_left] at this
      rw [this, hdg]
    · let τ1 := Equiv.swap i₀ i
      have hτk : τ1 k ≠ i := by
        intro h
        apply hk0
        have := congrArg τ1 h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      let σ := Equiv.swap (τ1 k) j * τ1
      have hσ0 : σ i₀ = i := by
        simp only [σ, τ1, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτk) hij
      have hσk : σ k = j := by
        simp only [σ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have := hB σ i₀ k
      rw [hσ0, hσk] at this
      rw [this, hoff]
  have hzero : polarBilin Q = 0 := by
    apply LinearMap.BilinForm.ext_basis f
    intro i j
    rw [polarBilin_apply_apply, LinearMap.zero_apply, LinearMap.zero_apply]
    exact hall i j
  have hf : f ⟨0, by omega⟩ ≠ 0 := f.ne_zero _
  apply hf
  apply hQ.1
  intro y
  rw [hzero, LinearMap.zero_apply, LinearMap.zero_apply]


theorem two_ne_zero_of (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem three_ne_zero_of (hp5 : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-- The Zalesskiĭ–Serežkin families for a reflection group in `O(V)` with a product of two reflections of
order `p ≥ 5`, in dimension at least four: only the Weyl groups, `O(V)` and the class closures remain. -/
theorem family_cases (hp5 : 5 ≤ p) (hQ : (polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hAO : A ≤ orthGroup Q) (hirr : IsIrreducible A) {a : U} (ha : Q a ≠ 0) (haA : reflect Q a ∈ A)
    (hdim : 4 ≤ finrank (ZMod p) U)
    (hpair : ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p)
    (hF : Family p A) :
    LinWeyl p A ∨ (∀ g, g ∈ A ↔ g ∈ orthGroup Q) ∨ (∃ c : ZMod p, c ≠ 0 ∧ A = classClosure Q c) := by
  have h2 := two_ne_zero_of hp5
  obtain ⟨x, hxA, y, hyA, hx, hy, hxy⟩ := hpair
  have hle : ∀ d, DMax p A d → p ≤ d := fun d hd => hxy ▸ hd.1 x hxA y hyA hx hy
  cases hF with
  | weyl h => exact Or.inl h
  | slpm h =>
    exfalso
    obtain ⟨v, hv⟩ : ∃ v : U, v ≠ 0 :=
      Module.finrank_pos_iff_exists_ne_zero.mp (lt_of_lt_of_le (by norm_num) hdim)
    have hlt : (ZMod p) ∙ v < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      have := finrank_span_singleton (K := ZMod p) hv
      rw [h, finrank_top] at this
      omega
    obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
    have hφv : φ v = 0 := hker (Submodule.mem_span_singleton_self v)
    let τ : U ≃ₗ[ZMod p] U := LinearEquiv.transvection hφv
    have hτ : ∀ z, τ z = z + φ z • v := fun z => rfl
    have hdet : LinearEquiv.det τ = 1 := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      change LinearMap.det (LinearMap.transvection φ v) = _
      rw [LinearMap.transvection.det, hφv, add_zero, Units.val_one]
    have hτA : τ ∈ A := (h τ).2 (Or.inl hdet)
    exact transvection_not_isometry h2 hQ hv hφ hφv fun z => by
      rw [← hτ]; exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hAO hτA) z
  | orth Q' hQ' hiff =>
    right; left
    obtain ⟨c, hc, hQc⟩ := exists_eq_smul_of_invariant h2 hQ hAO hirr ha haA hQ'
      (fun g hg => (hiff g).1 hg)
    intro g
    rw [hiff g]
    constructor
    · intro h v
      have := h v
      rw [hQc, hQc] at this
      exact mul_left_cancel₀ hc this
    · intro h v
      change Q' (g v) = Q' v
      rw [hQc, hQc, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup h]
  | orthClass Q' c hQ' hc hAeq =>
    right; right
    have hA' : ∀ g ∈ A, ∀ v, Q' (g v) = Q' v := by
      intro g hg
      rw [hAeq] at hg
      induction hg using Subgroup.closure_induction with
      | mem t ht => exact ht.2.1
      | one => intro v; rfl
      | mul a b _ _ ha' hb' => intro v; rw [LinearEquiv.mul_apply, ha', hb']
      | inv a _ ha' =>
        intro v
        have := ha' (a⁻¹ v)
        rw [apply_inv_apply] at this
        exact this.symm
    obtain ⟨μ, hμ, hQμ⟩ := exists_eq_smul_of_invariant h2 hQ hAO hirr ha haA hQ' hA'
    refine ⟨c / μ, div_ne_zero hc hμ, ?_⟩
    rw [hAeq, classClosure]
    congr 1
    ext t
    constructor
    · rintro ⟨htR, htI, a', ha'c, hta'⟩
      have htO : t ∈ orthGroup Q := fun v => by
        have := htI v
        rw [hQμ, hQμ] at this
        exact mul_left_cancel₀ hμ this
      obtain ⟨b, hb, rfl⟩ := (isInvRankOne_iff h2 hQ htO).1 htR
      obtain ⟨m, hm⟩ := mem_span_of_reflect_eq_neg h2 hb hta'
      have hQa : Q a' = c / μ := by
        rw [eq_div_iff hμ, mul_comm, ← hQμ, ha'c]
      have ha0 : a' ≠ 0 := by
        rintro rfl
        rw [QuadraticMap.map_zero] at hQa
        exact div_ne_zero hc hμ hQa.symm
      have hm0 : m ≠ 0 := by rintro rfl; rw [zero_smul] at hm; exact ha0 hm
      refine ⟨a', hQa, ?_⟩
      rw [hm, reflect_smul Q hm0]
    · rintro ⟨x, hx, rfl⟩
      have hx0 : Q x ≠ 0 := by rw [Set.mem_setOf_eq.mp hx]; exact div_ne_zero hc hμ
      refine ⟨(isInvRankOne_iff h2 hQ (reflect_mem Q x)).2 ⟨x, hx0, rfl⟩, fun v => ?_, x, ?_,
        reflect_apply_self Q hx0⟩
      · rw [hQμ, hQμ, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (reflect_mem Q x)]
      · rw [hQμ, Set.mem_setOf_eq.mp hx]
        field_simp
  | @gmmn n f i₀ i₁ ζ m h01 hm hord hAeq =>
    exfalso
    have hn : 3 ≤ (Fintype.card (Fin n)) := by
      rw [← Module.finrank_eq_card_basis f]; omega
    rw [Fintype.card_fin] at hn
    refine monomial_false (by omega) hQ f hn h01 (ζ := ζ) ?_ (fun σ => hAO ?_) (hAO ?_)
    · intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · rw [hAeq]; exact Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
    · rw [hAeq]; exact Subgroup.subset_closure (Or.inr rfl)
  | @g2mmn n f i₀ i₁ ζ m h01 hm hord hAeq =>
    exfalso
    have hn : 3 ≤ (Fintype.card (Fin n)) := by
      rw [← Module.finrank_eq_card_basis f]; omega
    rw [Fintype.card_fin] at hn
    refine monomial_false (by omega) hQ f hn h01 (ζ := ζ) ?_ (fun σ => hAO ?_) (hAO ?_)
    · intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hord] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · rw [hAeq]; exact Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)
    · rw [hAeq]; exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  | exc k hk hdeg _ _ hD _ _ =>
    exfalso
    have := hle _ hD
    cases k <;> simp only [ExcRow.dmax, ExcRow.admissible, ExcRow.deg] at this hk hdeg <;> omega
  | h4 hp5' _ _ _ hD _ =>
    exfalso
    have := hle _ hD
    omega

end Families

end CFSGOutside.HallOrthogonal
