import CFSGOutside.Gagola.Clifford

/-!
# Representation-level facts behind the special-element calculus

Three consequences of Schur's lemma, used to set up Gagola's special elements (§3) for an invariant
character of a normal subgroup that need not be central:

* `isIrreducible_of_character_mem_irr`: a representation with an irreducible character is irreducible;
* `sum_mul_char_of_normal`: for `N ⊴ G`, `θ` a `G`-invariant class function of `N` and `χ ∈ Irr G`,
  `χ(1) ∑ₙ θ(n⁻¹) χ(ng) = |N| ⟨χ_N, θ⟩ χ(g)` (the central element `∑ θ(n⁻¹) n` acts by a scalar);
* `ext_proportional`: two extensions `ψ, ψ'` of `θ` to `A ⊇ M` agree up to a scalar `z` on the
  powers `a^k` of an element normalizing `M`: `ψ'(a^k m) = z^k ψ(a^k m)`.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical Module

noncomputable section

section Irreducible

variable {M : Type*} [Group M] [Fintype M]

/-- A representation whose character is irreducible is irreducible. -/
theorem isIrreducible_of_character_mem_irr {m : ℕ} (σ : Representation ℂ M (Fin m → ℂ))
    (h : σ.character ∈ Irr M) : σ.IsIrreducible := by
  obtain ⟨n, X, hX, hXσ⟩ := h
  haveI := hX
  have hfin : finrank ℂ (X.IntertwiningMap σ) = 1 := by
    have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank X σ
    have h2 := ip_irr_self (⟨n, X, hX, rfl⟩ : X.character ∈ Irr M)
    simp only [ip] at h2
    rw [← hXσ, h2] at h1
    exact_mod_cast h1.symm
  have hnt : Nontrivial (X.IntertwiningMap σ) := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨f, hf0⟩ := exists_ne (0 : X.IntertwiningMap σ)
  have hfinj : Function.Injective f := (hX.injective_or_eq_zero f).resolve_right hf0
  have hdim : finrank ℂ (Fin n → ℂ) = finrank ℂ (Fin m → ℂ) := by
    have h1 := congrFun hXσ 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1
  have hfsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).mp hfinj
  let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsurj⟩
  refine Representation.isIrreducible_of_linearEquiv e (fun g v => ?_) hX
  exact LinearMap.congr_fun (f.isIntertwining' g) v

/-- **Generalized orthogonality** in operator form: `χ(1) ∑ₓ χ(x⁻¹) σ(x) = |M| · 1`. -/
theorem char_one_smul_sum {m : ℕ} (σ : Representation ℂ M (Fin m → ℂ)) [hσ : σ.IsIrreducible] :
    σ.character 1 • ∑ x : M, σ.character x⁻¹ • σ x = (Nat.card M : ℂ) • (1 : Module.End ℂ _) := by
  set T : Module.End ℂ (Fin m → ℂ) := ∑ x : M, σ.character x⁻¹ • σ x with hT
  have hcommE : ∀ g, T * σ g = σ g * T := by
    intro g
    rw [hT, Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ (fun x => ?_)
    show σ.character x⁻¹ • σ x * σ g = σ g * (σ.character (g⁻¹ * x * g⁻¹⁻¹)⁻¹ • σ (g⁻¹ * x * g⁻¹⁻¹))
    rw [inv_inv, smul_mul_assoc, mul_smul_comm]
    have h1 : σ.character (g⁻¹ * x * g)⁻¹ = σ.character x⁻¹ := by
      rw [show (g⁻¹ * x * g)⁻¹ = g⁻¹ * x⁻¹ * g⁻¹⁻¹ by group, Representation.char_conj]
    rw [h1, ← map_mul, ← map_mul]
    congr 2; group
  have hcomm : ∀ g v, T (σ g v) = σ g (T v) := fun g v => LinearMap.congr_fun (hcommE g) v
  obtain ⟨c, hc⟩ := hσ.exists_forall_apply_eq_smul T hcomm
  have hTc : T = c • (1 : Module.End ℂ _) := LinearMap.ext fun v => by rw [hc v]; simp
  have htr : LinearMap.trace ℂ _ T = Nat.card M := by
    have h2 := ip_irr_self (⟨m, σ, hσ, rfl⟩ : σ.character ∈ Irr M)
    simp only [ip] at h2
    have hM : (Nat.card M : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [hT, map_sum]
    simp only [map_smul, smul_eq_mul]
    have : ∑ x : M, σ.character x⁻¹ * LinearMap.trace ℂ _ (σ x) =
        ∑ x : M, σ.character x * σ.character x⁻¹ := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm]; rfl
    rw [this]
    field_simp at h2
    linear_combination h2
  have htr' : LinearMap.trace ℂ _ T = c * σ.character 1 := by
    rw [hTc, map_smul, LinearMap.trace_one, Representation.char_one, smul_eq_mul]
  rw [hTc, smul_smul, mul_comm, ← htr', htr]

end Irreducible

section Normal

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [hN : N.Normal]

/-- **The central idempotent of an invariant class function.** For `N ⊴ G`, `θ` a `G`-invariant
class function of `N` and `χ ∈ Irr G`: `χ(1) ∑ₙ θ(n⁻¹) χ(n g) = |N| ⟨χ_N, θ⟩ χ(g)`. -/
theorem sum_mul_char_of_normal {θ : N → ℂ} (hinv : ∀ x : G, conjN N x θ = θ)
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (g : G) :
    χ 1 * ∑ n : N, θ n⁻¹ * χ (n * g) = (Nat.card N : ℂ) * ip (pull N.subtype χ) θ * χ g := by
  obtain ⟨m, ρ, hρ, rfl⟩ := hχ
  haveI := hρ
  set T : Module.End ℂ (Fin m → ℂ) := ∑ n : N, θ n⁻¹ • ρ n with hT
  have hcommE : ∀ x, T * ρ x = ρ x * T := by
    intro x
    rw [hT, Finset.sum_mul, Finset.mul_sum]
    -- reindex by `n ↦ x n x⁻¹`
    let e : N ≃ N :=
      { toFun := fun n => ⟨x * n * x⁻¹, hN.conj_mem n n.2 x⟩
        invFun := fun n => ⟨x⁻¹ * n * x, by simpa using hN.conj_mem n n.2 x⁻¹⟩
        left_inv := fun n => by ext; simp [mul_assoc]
        right_inv := fun n => by ext; simp [mul_assoc] }
    refine (Fintype.sum_equiv e _ _ (fun n => ?_)).symm
    show ρ x * (θ n⁻¹ • ρ n) = θ (⟨x * n * x⁻¹, hN.conj_mem n n.2 x⟩ : N)⁻¹ •
      ρ (⟨x * n * x⁻¹, hN.conj_mem n n.2 x⟩ : N) * ρ x
    rw [smul_mul_assoc, mul_smul_comm]
    have hθ : θ (⟨x * n * x⁻¹, hN.conj_mem n n.2 x⟩ : N)⁻¹ = θ n⁻¹ := by
      have := congrFun (hinv x⁻¹) n⁻¹
      simp only [conjN_apply, inv_inv] at this
      rw [← this]
      congr 1; ext; simp [mul_assoc]
    rw [hθ, ← map_mul, ← map_mul]
    congr 2
    simp [mul_assoc]
  have hcomm : ∀ x v, T (ρ x v) = ρ x (T v) := fun x v => LinearMap.congr_fun (hcommE x) v
  obtain ⟨c, hc⟩ := hρ.exists_forall_apply_eq_smul T hcomm
  have hTc : T = c • (1 : Module.End ℂ _) := LinearMap.ext fun v => by rw [hc v]; simp
  have hsum : ∀ y : G, ∑ n : N, θ n⁻¹ * ρ.character (n * y) =
      LinearMap.trace ℂ _ (T * ρ y) := by
    intro y
    rw [hT, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]
    rfl
  have h1 : ∑ n : N, θ n⁻¹ * ρ.character (n * g) = c * ρ.character g := by
    rw [hsum, hTc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl
  have h2 : ∑ n : N, θ n⁻¹ * ρ.character (n * 1) = c * ρ.character 1 := by
    rw [hsum, hTc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl
  have hip : (Nat.card N : ℂ) * ip (pull N.subtype ρ.character) θ =
      ∑ n : N, θ n⁻¹ * ρ.character (n * 1) := by
    have hN0 : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    simp only [ip, pull_apply, Subgroup.coe_subtype, mul_one]
    rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  rw [hip, h1, h2]
  ring

end Normal

section Proportional

variable {A M : Type*} [Group A] [Fintype A] [Group M] [Fintype M]

/-- **Two extensions of an irreducible character differ by a scalar along a normalizing element.**
Let `ι : M → A`, `a ∈ A` with `a⁻¹ ι(m) a = ι(c m)`, `θ ∈ Irr M`, and `ψ, ψ' ∈ Irr A` both restricting
to `θ`. Then there is `z` with `ψ'(a^k ι(m)) = z^k ψ(a^k ι(m))` for all `k`, `m`. -/
theorem ext_proportional (ι : M →* A) (c : M →* M) (a : A) (hc : ∀ m, ι (c m) = a⁻¹ * ι m * a)
    {θ : M → ℂ} (hθ : θ ∈ Irr M) {ψ ψ' : A → ℂ} (hψ : ψ ∈ Irr A) (hψ' : ψ' ∈ Irr A)
    (h1 : pull ι ψ = θ) (h2 : pull ι ψ' = θ) :
    ∃ z : ℂ, ∀ (k : ℕ) (m : M), ψ' (a ^ k * ι m) = z ^ k * ψ (a ^ k * ι m) := by
  obtain ⟨d, ρ, hρ, rfl⟩ := hψ
  obtain ⟨d', ρ', hρ', rfl⟩ := hψ'
  set ρι : Representation ℂ M (Fin d → ℂ) := ρ.comp ι
  set ρ'ι : Representation ℂ M (Fin d' → ℂ) := ρ'.comp ι
  have hcι : ρι.character = θ := by funext m; exact congrFun h1 m
  have hc'ι : ρ'ι.character = θ := by funext m; exact congrFun h2 m
  haveI hι : ρι.IsIrreducible := isIrreducible_of_character_mem_irr ρι (hcι ▸ hθ)
  haveI hι' : ρ'ι.IsIrreducible := isIrreducible_of_character_mem_irr ρ'ι (hc'ι ▸ hθ)
  -- an `M`-isomorphism `e : ρι ≅ ρ'ι`
  have hfin : finrank ℂ (ρι.IntertwiningMap ρ'ι) = 1 := by
    have h1 := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρι ρ'ι
    have h2 := ip_irr_self hθ
    simp only [ip] at h2
    rw [hcι, hc'ι, h2] at h1
    exact_mod_cast h1.symm
  have hnt : Nontrivial (ρι.IntertwiningMap ρ'ι) := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨f, hf0⟩ := exists_ne (0 : ρι.IntertwiningMap ρ'ι)
  have hfb : Function.Bijective f := (hι.bijective_or_eq_zero f).resolve_right hf0
  let e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ) := LinearEquiv.ofBijective f.toLinearMap hfb
  have he : ∀ m v, e (ρ (ι m) v) = ρ' (ι m) (e v) := fun m v =>
    LinearMap.congr_fun (f.isIntertwining' m) v
  have he' : ∀ m v, e.symm (ρ' (ι m) v) = ρ (ι m) (e.symm v) := by
    intro m v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  -- `S = e⁻¹ ρ'(a) e ρ(a)⁻¹` commutes with `ρ ∘ ι`
  set S : Module.End ℂ (Fin d → ℂ) :=
    e.symm.toLinearMap ∘ₗ ρ' a ∘ₗ e.toLinearMap ∘ₗ ρ a⁻¹ with hS
  have hSc : ∀ m v, S (ρι m v) = ρι m (S v) := by
    intro m v
    simp only [hS, ρι, MonoidHom.coe_comp, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe]
    have k1 : ρ a⁻¹ (ρ (ι m) v) = ρ (ι (c m)) (ρ a⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc]
      congr 2; group
    have k2 : ρ' a (ρ' (ι (c m)) (e (ρ a⁻¹ v))) = ρ' (ι m) (ρ' a (e (ρ a⁻¹ v))) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (ρ' (ι m)), ← map_mul, hc]
      congr 2; group
    rw [k1, he, k2, he']
  obtain ⟨z, hz⟩ := hι.exists_forall_apply_eq_smul S hSc
  have hstep : ∀ v, e.symm (ρ' a (e v)) = z • ρ a v := by
    intro v
    have := hz (ρ a v)
    simp only [hS, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have hpow : ∀ (k : ℕ) v, e.symm (ρ' (a ^ k) (e v)) = z ^ k • ρ (a ^ k) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have hav : ρ' a (e v) = e (z • ρ a v) := by rw [← hstep v, LinearEquiv.apply_symm_apply]
      calc e.symm (ρ' (a ^ (k + 1)) (e v)) = e.symm (ρ' (a ^ k) (ρ' a (e v))) := by
            rw [pow_succ, map_mul, Module.End.mul_apply]
        _ = z • e.symm (ρ' (a ^ k) (e (ρ a v))) := by rw [hav, map_smul, map_smul, map_smul]
        _ = z ^ (k + 1) • ρ (a ^ (k + 1)) v := by
            rw [ih, smul_smul, pow_succ, pow_succ, map_mul, Module.End.mul_apply, mul_comm]
  refine ⟨z, fun k m => ?_⟩
  have hconj : (e.symm.toLinearMap ∘ₗ ρ' (a ^ k * ι m) ∘ₗ e.toLinearMap) =
      z ^ k • ρ (a ^ k * ι m) := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, map_mul,
      Module.End.mul_apply, LinearMap.smul_apply]
    rw [← he, hpow]
  have htr := LinearMap.trace_conj' (ρ' (a ^ k * ι m)) e.symm
  simp only [Representation.character]
  rw [← htr, LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_assoc, hconj, map_smul,
    smul_eq_mul]

/-- For an extension `ψ ∈ Irr A` of `θ ∈ Irr M`: `θ(1) ∑ₘ θ(m⁻¹) ψ(ι(m) l) = |M| ψ(l)`. -/
theorem ext_sum (ι : M →* A) {θ : M → ℂ} (hθ : θ ∈ Irr M) {ψ : A → ℂ} (hψ : ψ ∈ Irr A)
    (h1 : pull ι ψ = θ) (l : A) :
    θ 1 * ∑ m : M, θ m⁻¹ * ψ (ι m * l) = Nat.card M * ψ l := by
  obtain ⟨d, ρ, hρ, rfl⟩ := hψ
  set σ : Representation ℂ M (Fin d → ℂ) := ρ.comp ι
  have hσc : σ.character = θ := by funext m; exact congrFun h1 m
  haveI : σ.IsIrreducible := isIrreducible_of_character_mem_irr σ (hσc ▸ hθ)
  have key := char_one_smul_sum σ
  rw [hσc] at key
  have := congrArg (fun T : Module.End ℂ (Fin d → ℂ) => LinearMap.trace ℂ _ (T * ρ l)) key
  simp only [smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, smul_eq_mul, one_mul] at this
  convert this using 2
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Representation.character, σ, MonoidHom.coe_comp, Function.comp_apply, map_mul]
  · rfl

/-- An extension `ψ ∈ Irr A` of `θ ∈ Irr M` does not vanish on any coset `a ι(M)`. -/
theorem exists_ne_zero_coset (ι : M →* A) {θ : M → ℂ} (hθ : θ ∈ Irr M) {ψ : A → ℂ}
    (hψ : ψ ∈ Irr A) (h1 : pull ι ψ = θ) (a : A) : ∃ m : M, ψ (a * ι m) ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨d, ρ, hρ, rfl⟩ := hψ
  set σ : Representation ℂ M (Fin d → ℂ) := ρ.comp ι
  have hσc : σ.character = θ := by funext m; exact congrFun h1 m
  have hσ : σ.IsIrreducible := isIrreducible_of_character_mem_irr σ (hσc ▸ hθ)
  obtain ⟨x, hx⟩ := Representation.asAlgebraHom_surjective_of_isIrreducible σ hσ (ρ a⁻¹)
  -- the functional `X ↦ tr (ρ(a) X)` kills the image of the group algebra
  have hzero : ∀ y : MonoidAlgebra ℂ M, LinearMap.trace ℂ _ (ρ a * σ.asAlgebraHom y) = 0 := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of m =>
      rw [Representation.asAlgebraHom_of]
      have : ρ a * σ m = ρ (a * ι m) := by
        simp only [σ, MonoidHom.coe_comp, Function.comp_apply, map_mul]
      rw [this]
      exact hall m
    | add y₁ y₂ h₁ h₂ => rw [map_add, mul_add, map_add, h₁, h₂, add_zero]
    | smul r y h => rw [map_smul, mul_smul_comm, map_smul, h, smul_zero]
  have := hzero x
  rw [hx, ← map_mul, mul_inv_cancel, map_one, LinearMap.trace_one] at this
  have hd : 0 < Module.finrank ℂ (Fin d → ℂ) := hρ.finrank_pos
  exact hd.ne' (by exact_mod_cast this)

end Proportional

end

end CFSGOutside.Gagola
