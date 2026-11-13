import CFSGOutside.Gagola.Special
import CFSGOutside.Gagola.ModP
import CFSGOutside.Gagola.GroupFacts

/-!
# Lemmas for Gagola's Corollary 3.6 and Lemma 4.4

* `irr_eq_of_special_le`: if every special element lies in `N`, then `θ` lies under at most one
  irreducible character (the part of Gagola's Theorem 3.1 used in Corollary 3.6).
* `nonfusion`: if every class function in the span of `Irr (D | θ)` is the restriction of a class
  function of an overgroup `K`, then a special element of `D` can only be fused in `K` into its own
  `D`-class (modulo `N`). This is the part of Gagola's Theorem 3.5 used in Corollary 3.6 and
  Lemma 4.4; the restriction hypothesis replaces his matrix argument (Theorem 3.4).
* `thetaPair`, `fr_ip_pull_mul`: Gagola's Lemma 2.1(a)–(c) for a subgroup given as the image of an
  injective homomorphism.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

section Special

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [hN : N.Normal] {θ : N → ℂ}

/-- If every special element lies in `N`, any two irreducible characters over `θ` coincide. -/
theorem irr_eq_of_special_le (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ)
    (hsp : ∀ g : G, IsSpecial θ g → g ∈ N) {χ χ' : G → ℂ} (hχ : χ ∈ Irr G) (hχ' : χ' ∈ Irr G)
    (hover : mult (pull N.subtype χ) θ ≠ 0) (hover' : mult (pull N.subtype χ') θ ≠ 0) :
    χ = χ' := by
  set m := mult (pull N.subtype χ) θ
  set m' := mult (pull N.subtype χ') θ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hover
  -- `χ' = (m'/m) χ`
  have hprop : χ' = ((m' : ℂ) / m) • χ := by
    funext y
    by_cases hy : y ∈ N
    · have h1 := congrFun (res_eq_mult_smul hθ hinv hχ hover) ⟨y, hy⟩
      have h2 := congrFun (res_eq_mult_smul hθ hinv hχ' hover') ⟨y, hy⟩
      simp only [pull_apply, Subgroup.coe_subtype, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      rw [h1, h2]; field_simp; ring
    · have h1 := char_eq_zero_of_not_special hθ hinv hχ hover (fun h => hy (hsp y h))
      have h2 := char_eq_zero_of_not_special hθ hinv hχ' hover' (fun h => hy (hsp y h))
      simp [h1, h2]
  by_contra hne
  have h0 := ip_irr hχ' hχ
  rw [if_neg (Ne.symm hne), hprop, ip_smul_left, ip_irr_self hχ, mul_one] at h0
  have hm'0 : (m' : ℂ) ≠ 0 := by exact_mod_cast hover'
  exact div_ne_zero hm'0 hm0 h0

/-- **Gagola, Theorem 3.1 (one inequality).** Pairwise non-fused special elements are at most as many
as the irreducible characters over `θ`. -/
theorem card_special_le (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := G) θ) (T : Finset G)
    (hT : ∀ x ∈ T, IsSpecial θ x)
    (hdis : ∀ x ∈ T, ∀ y ∈ T, (∃ u : G, u⁻¹ * y * u * x⁻¹ ∈ N) → x = y) :
    T.card ≤ ((irrFinset G).filter fun χ => mult (pull N.subtype χ) θ ≠ 0).card := by
  choose ψ hψ using fun x : T => exists_ext hθ hinv (x : G)
  choose m hm using fun x : T => exists_ne_zero_coset (inclN N (x : G)) hθ (hψ x).1 (hψ x).2
    (gen (N := N) (x : G))
  set F : T → G → ℂ := fun x => specialFn (x : G) (ψ x)
  have hm' : ∀ x : T, ext0 (ψ x) ((x : G) * m x) ≠ 0 := by
    intro x
    rw [ext0_of_mem _ (mul_mem_cycN _ _)]
    convert hm x using 2
    ext; rfl
  have hval : ∀ x y : T, F y ((x : G) * m x) = if x = y then ext0 (ψ x) ((x : G) * m x) else 0 := by
    intro x y
    split_ifs with hxy
    · subst hxy
      exact specialFn_mul (hT x x.2) (hψ x) (m x)
    · apply specialFn_of_not
      rintro ⟨u, hu⟩
      apply hxy
      refine Subtype.ext (hdis y y.2 x x.2 ⟨u, ?_⟩).symm
      have : u⁻¹ * (x : G) * u * (y : G)⁻¹ =
          (u⁻¹ * ((x : G) * m x) * u * (y : G)⁻¹) * ((y : G) * (u⁻¹ * (m x : G)⁻¹ * u) * (y : G)⁻¹) := by
        group
      rw [this]
      refine N.mul_mem hu ?_
      exact hN.conj_mem _ (conj_inv_mem N u (m x)⁻¹) _
  have hli : LinearIndependent ℂ F := by
    rw [linearIndependent_iff']
    intro t c hc x hx
    have := congrFun hc ((x : G) * m x)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hval] at this
    rw [Finset.sum_eq_single x (fun y _ hyx => by rw [if_neg (Ne.symm hyx), mul_zero])
      (fun h => absurd hx h), if_pos rfl] at this
    exact (mul_eq_zero.mp this).resolve_right (hm' x)
  have hsub : Set.range F ⊆ (spanOver (G := G) θ : Set (G → ℂ)) := by
    rintro _ ⟨x, rfl⟩
    exact specialFn_mem_spanOver hθ hinv (hT x x.2) (hψ x)
  have := linearIndependent_le_span' F hli
    (((irrFinset G).filter fun χ => mult (pull N.subtype χ) θ ≠ 0 : Finset _) : Set (G → ℂ)) hsub
  rw [Cardinal.mk_fintype] at this
  have h2 : Fintype.card T = T.card := Fintype.card_coe T
  have h3 : Fintype.card ↥(((irrFinset G).filter fun χ => mult (pull N.subtype χ) θ ≠ 0 :
      Finset _) : Set (G → ℂ)) = ((irrFinset G).filter fun χ => mult (pull N.subtype χ) θ ≠ 0).card :=
    by simp
  rw [h2, h3] at this
  exact_mod_cast this

/-- The span of `Irr (G | θ)` consists of class functions. -/
theorem isClassFn_of_mem_spanOver {f : G → ℂ} (hf : f ∈ spanOver (G := G) θ) : IsClassFn f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    exact irr_isClassFn (mem_irrFinset.mp (Finset.mem_filter.mp hx).1)
  | zero => exact isClassFn_zero
  | add x y _ _ hx hy => exact isClassFn_add hx hy
  | smul c x _ hx => exact isClassFn_smul c hx

end Special

section Nonfusion

variable {K D : Type*} [Group K] [Fintype K] [Group D] [Fintype D] {N : Subgroup D} [hN : N.Normal]
  {θ : N → ℂ}

/-- **Non-fusion.** Let `ι : D → K` and suppose every class function in the span of `Irr (D | θ)`
is the restriction of a class function of `K`. Then for each special `g ∈ D` there is `m ∈ N` such
that every `K`-conjugate of `g m` lying in `ι(D)` is the image of a `D`-conjugate of an element of
`g N`. -/
theorem nonfusion (ι : D →* K) (hθ : θ ∈ Irr N) (hinv : IsInvariant (G := D) θ)
    (hsurj : ∀ φ ∈ spanOver (G := D) θ, ∃ f : K → ℂ, IsClassFn f ∧ pull ι f = φ) {g : D}
    (hsp : IsSpecial θ g) :
    ∃ m : N, ∀ (x : K) (d' : D), x * ι (g * m) * x⁻¹ = ι d' → ∃ u : D, u⁻¹ * d' * u * g⁻¹ ∈ N := by
  obtain ⟨ψ, hψ⟩ := exists_ext hθ hinv g
  obtain ⟨m, hm⟩ := exists_ne_zero_coset (inclN N g) hθ hψ.1 hψ.2 (gen (N := N) g)
  have hm' : ext0 ψ (g * m) ≠ 0 := by
    rw [ext0_of_mem _ (mul_mem_cycN g m)]
    convert hm using 2
    ext; rfl
  obtain ⟨f, hf, hfF⟩ := hsurj _ (specialFn_mem_spanOver hθ hinv hsp hψ)
  refine ⟨m, fun x d' hd' => ?_⟩
  by_contra hno
  push Not at hno
  have hF0 : specialFn g ψ d' = 0 := specialFn_of_not (fun ⟨u, hu⟩ => hno u hu)
  have h1 : specialFn g ψ d' = f (ι d') := by rw [← hfF]; rfl
  have h2 : f (ι d') = f (ι (g * m)) := by
    rw [← hd']
    exact hf _ x
  have h3 : f (ι (g * m)) = specialFn g ψ (g * m) := by rw [← hfF]; rfl
  rw [h1, h2, h3, specialFn_mul hsp hψ] at hF0
  exact hm' hF0

end Nonfusion

section Theta

variable {H : Type*} [Group H] [Fintype H] {Z : Subgroup H} {χ : H → ℂ} {θ : Z → ℂ} {e : ℕ}

/-- The pairing of a function on `M ⊇ Z` with `θ`: `Θ(f) = |Z|⁻¹ ∑_z f(z) θ(z⁻¹)`, where `s : Z → M`
is the inclusion. -/
def thetaPair {M : Type*} [Group M] (θ : Z → ℂ) (s : Z →* M) (f : M → ℂ) : ℂ :=
  (Nat.card Z : ℂ)⁻¹ * ∑ z : Z, f (s z) * θ z⁻¹

theorem thetaPair_add {M : Type*} [Group M] (s : Z →* M) (f f' : M → ℂ) :
    thetaPair θ s (f + f') = thetaPair θ s f + thetaPair θ s f' := by
  simp only [thetaPair, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem thetaPair_smul {M : Type*} [Group M] (s : Z →* M) (c : ℂ) (f : M → ℂ) :
    thetaPair θ s (c • f) = c * thetaPair θ s f := by
  simp only [thetaPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => by ring

theorem thetaPair_sum {M : Type*} [Group M] {ι : Type*} (s : Z →* M) (t : Finset ι)
    (f : ι → M → ℂ) : thetaPair θ s (∑ i ∈ t, f i) = ∑ i ∈ t, thetaPair θ s (f i) := by
  induction t using Finset.induction_on with
  | empty => simp [thetaPair]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaPair_add, ih]

theorem thetaPair_pull {M M' : Type*} [Group M] [Group M'] (s : Z →* M) (s' : Z →* M')
    (j : M →* M') (hj : ∀ z, j (s z) = s' z) (f : M' → ℂ) :
    thetaPair θ s (pull j f) = thetaPair θ s' f := by
  simp only [thetaPair, pull_apply, hj]

/-- **Gagola, Lemma 2.1(a)–(c)** for `ι : M → H` injective with `Z ≤ ι(M)`:
`⟨χ_M, ξ⟩ |M| = e |Z| Θ(ξ)`. -/
theorem fr_ip_pull_mul (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) {M : Type*} [Group M] [Fintype M] (ι : M →* H)
    (hι : Function.Injective ι) (s : Z →* M) (hs : ∀ z, ι (s z) = z) (ξ : M → ℂ) :
    ip (pull ι χ) ξ * Nat.card M = e * Nat.card Z * thetaPair θ s ξ := by
  have hM : (Nat.card M : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hZc : (Nat.card Z : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsinj : Function.Injective s := fun a b h => Subtype.ext (by rw [← hs a, ← hs b, h])
  simp only [ip, thetaPair, pull_apply]
  have h1 : ∑ m : M, χ (ι m) * ξ m⁻¹ = ∑ z : Z, χ (ι (s z)) * ξ (s z)⁻¹ := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨s, hsinj⟩))]
    · rw [Finset.sum_map]; rfl
    · intro m _ hm
      have : ι m ∉ Z := by
        intro hz
        apply hm
        refine Finset.mem_map.mpr ⟨⟨ι m, hz⟩, Finset.mem_univ _, hι ?_⟩
        simp [hs]
      simp [fr_vanish hχ hθ hres he this]
  have h2 : ∀ z : Z, χ (ι (s z)) = e * θ z := fun z => by
    have := congrFun hres z; rw [hs]; simpa using this
  rw [h1]
  simp_rw [h2]
  rw [show ∑ z : Z, (e : ℂ) * θ z * ξ (s z)⁻¹ = e * ∑ z : Z, ξ (s z) * θ z⁻¹ from ?_]
  · field_simp
  · rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.inv Z) _ _ (fun z => ?_)
    simp only [Equiv.inv_apply, inv_inv, map_inv]
    ring

end Theta

end

end CFSGOutside.Gagola
