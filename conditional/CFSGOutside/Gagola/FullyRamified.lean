import CFSGOutside.Gagola.Clifford
import TauCeti.RepresentationTheory.CharacterTable.Values

/-!
# Fully ramified triples (Gagola 1974, §§1–2)

`(H, Z, χ)` is a *fully ramified triple* if `Z ⊴ H`, `χ ∈ Irr H` and `χ_Z = e θ` with `θ ∈ Irr Z` and
`e² = |H : Z|`. A group is *of type f.r.* if it is isomorphic to `H/Z` for such a triple.

This file proves the parts of Gagola's Lemma 2.1 and Lemma 2.2 that are used later:

* `fr_vanish`: `χ` vanishes off `Z`;
* `fr_ip_pull`: Lemma 2.1(d), `‖χ_L‖² = |H : L|` for `Z ≤ L`;
* `fr_ip_mul_card`: Lemma 2.1(a)–(b), `⟨χ_L, ζ⟩ |L| = e |Z| ⟨ζ_Z, θ⟩`;
* `fr_sylow`: Lemma 2.2 for a prime `p`: if `Z ≤ R`, `|R : Z|` is a power of `p` and `p ∤ |H : R|`, then
  `χ_R = a ζ` for a single `ζ ∈ Irr R`, with `a² = |H : R|`.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

/-- **Fully ramified triple** (Gagola, §1): `Z ⊴ H`, `χ ∈ Irr H`, and `χ_Z = e θ` with `θ ∈ Irr Z` and
`e² = |H : Z|`. -/
def FullyRamified {H : Type*} [Group H] [Fintype H] (Z : Subgroup H) (χ : H → ℂ) : Prop :=
  Z.Normal ∧ χ ∈ Irr H ∧
    ∃ (θ : Z → ℂ) (e : ℕ), θ ∈ Irr Z ∧ pull Z.subtype χ = (e : ℂ) • θ ∧ e ^ 2 = Z.index

/-- **Groups of type f.r.** (Gagola, §1): `G ≅ H/Z` for a fully ramified triple `(H, Z, χ)`. -/
def IsTypeFR (G : Type*) [Group G] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Fintype H) (Z : Subgroup H) (_ : Z.Normal) (χ : H → ℂ),
    FullyRamified Z χ ∧ Nonempty (G ≃* H ⧸ Z)

variable {H : Type*} [Group H] [Fintype H]

theorem irr_inv {χ : H → ℂ} (hχ : χ ∈ Irr H) (g : H) : χ g⁻¹ = starRingEnd ℂ (χ g) := by
  obtain ⟨n, ρ, -, rfl⟩ := hχ
  exact (TauCeti.Representation.conj_char ρ g).symm

theorem irr_mul_inv {χ : H → ℂ} (hχ : χ ∈ Irr H) (g : H) :
    χ g * χ g⁻¹ = ((Complex.normSq (χ g) : ℝ) : ℂ) := by
  rw [irr_inv hχ, Complex.mul_conj]

theorem sum_normSq_irr {χ : H → ℂ} (hχ : χ ∈ Irr H) :
    ∑ x : H, Complex.normSq (χ x) = Nat.card H := by
  have h := ip_irr_self hχ
  simp only [ip] at h
  have hG : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h2 : ∑ x : H, χ x * χ x⁻¹ = Nat.card H := by
    field_simp at h; linear_combination h
  simp_rw [irr_mul_inv hχ] at h2
  exact_mod_cast h2

section Triple

variable {Z : Subgroup H} {χ : H → ℂ} {θ : Z → ℂ} {e : ℕ}

theorem card_eq_sq_mul (he : e ^ 2 = Z.index) : Nat.card H = e ^ 2 * Nat.card Z := by
  rw [he, mul_comm, Subgroup.card_mul_index]

/-- The sum of `‖χ‖²` over `Z` is `|H|`. -/
theorem sum_normSq_Z (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ) (he : e ^ 2 = Z.index) :
    ∑ z : Z, Complex.normSq (χ z) = Nat.card H := by
  have h1 : ∀ z : Z, χ z = e * θ z := fun z => by
    have := congrFun hres z; simpa using this
  simp_rw [h1, Complex.normSq_mul, Complex.normSq_natCast, ← Finset.mul_sum, sum_normSq_irr hθ]
  rw [card_eq_sq_mul he]; push_cast; ring

/-- Gagola, Lemma 2.1 (proof): a fully ramified character vanishes off `Z`. -/
theorem fr_vanish (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) {h : H} (hh : h ∉ Z) : χ h = 0 := by
  have htot := sum_normSq_irr hχ
  have hZ := sum_normSq_Z hθ hres he
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : H => x ∈ Z)
    (fun x => Complex.normSq (χ x))
  have hsub : ∑ x ∈ Finset.univ.filter (fun x : H => x ∈ Z), Complex.normSq (χ x) =
      ∑ z : Z, Complex.normSq (χ z) :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [hsub, hZ, htot] at hsplit
  have hrest : ∑ x ∈ Finset.univ.filter (fun x : H => x ∉ Z), Complex.normSq (χ x) = 0 := by
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg _)).mp hrest h
    (by simp [hh])
  exact Complex.normSq_eq_zero.mp this

/-- A sum over `M` of a function vanishing off `Z ⊆ φ(M)` is the sum over `H`. -/
theorem sum_pull_of_vanish {M : Type*} [Group M] [Fintype M] {φ : M →* H}
    (hφ : Function.Injective φ) (hZ : Z ≤ φ.range) (g : H → ℝ) (hg : ∀ h, h ∉ Z → g h = 0) :
    ∑ m : M, g (φ m) = ∑ h : H, g h := by
  have hm := Finset.sum_map Finset.univ ⟨φ, hφ⟩ g
  simp only [Function.Embedding.coeFn_mk] at hm
  rw [← hm]
  refine Finset.sum_subset (Finset.subset_univ _) fun h _ hh => ?_
  refine hg h fun hz => hh ?_
  obtain ⟨m, rfl⟩ := hZ hz
  exact Finset.mem_map.mpr ⟨m, Finset.mem_univ _, rfl⟩

/-- Gagola, Lemma 2.1(d): for `Z ≤ L`, `‖χ_L‖² = |H : L|` (here `L` is the image of an injective
homomorphism). -/
theorem fr_ip_pull (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) {M : Type*} [Group M] [Fintype M] {φ : M →* H}
    (hφ : Function.Injective φ) (hZ : Z ≤ φ.range) :
    ip (pull φ χ) (pull φ χ) * Nat.card M = Nat.card H := by
  have hM : (Nat.card M : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp only [ip, pull_apply]
  have h1 : ∑ m : M, χ (φ m) * χ (φ m⁻¹) = ((∑ m : M, Complex.normSq (χ (φ m)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_inv, irr_mul_inv hχ]
  rw [h1, sum_pull_of_vanish hφ hZ (fun h => Complex.normSq (χ h)) (fun h hh => by
    rw [fr_vanish hχ hθ hres he hh]; simp), sum_normSq_irr hχ]
  push_cast
  field_simp

/-- Gagola, Lemma 2.1(a)–(c): for `Z ≤ L` and `ζ ∈ Irr L`,
`⟨χ_L, ζ⟩ |L| = e |Z| ⟨ζ_Z, θ⟩`. -/
theorem fr_ip_mul_card (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) {L : Subgroup H} (hZL : Z ≤ L) (ζ : L → ℂ) :
    ip (pull L.subtype χ) ζ * Nat.card L =
      e * Nat.card Z * ip (pull (Subgroup.inclusion hZL) ζ) θ := by
  have hL : (Nat.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hZc : (Nat.card Z : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp only [ip, pull_apply]
  -- the sum over `L` reduces to `Z`
  have h1 : ∑ l : L, χ (L.subtype l) * ζ l⁻¹ = ∑ z : Z, χ z * ζ (Subgroup.inclusion hZL z)⁻¹ := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨Subgroup.inclusion hZL,
      Subgroup.inclusion_injective hZL⟩))]
    · rw [Finset.sum_map]; rfl
    · intro l _ hl
      have : (l : H) ∉ Z := fun hz =>
        hl (Finset.mem_map.mpr ⟨⟨l, hz⟩, Finset.mem_univ _, by ext; rfl⟩)
      simp [fr_vanish hχ hθ hres he this]
  have h2 : ∀ z : Z, χ z = e * θ z := fun z => by
    have := congrFun hres z; simpa using this
  rw [h1]
  simp_rw [h2]
  rw [show ∑ z : Z, (e : ℂ) * θ z * ζ (Subgroup.inclusion hZL z)⁻¹ =
    e * ∑ z : Z, ζ (Subgroup.inclusion hZL z) * θ z⁻¹ from ?_]
  · field_simp
  · rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.inv Z) _ _ (fun z => ?_)
    simp only [Equiv.inv_apply, inv_inv, map_inv]
    ring

/-- Gagola, Lemma 2.2 for a Sylow-type subgroup: if `Z ≤ R`, `|R| = pᵏ |Z|` and `p ∤ |H : R|`, then
`χ_R = a ζ` for a single `ζ ∈ Irr R`, with `a² = |H : R|`. -/
theorem fr_sylow (hχ : χ ∈ Irr H) (hθ : θ ∈ Irr Z) (hres : pull Z.subtype χ = (e : ℂ) • θ)
    (he : e ^ 2 = Z.index) {R : Subgroup H} (hZR : Z ≤ R) {p k : ℕ} (hp : p.Prime)
    (hRZ : Nat.card R = p ^ k * Nat.card Z) (hpR : ¬ p ∣ R.index) :
    ∃ ζ ∈ Irr R, ∃ a : ℕ, pull R.subtype χ = (a : ℂ) • ζ ∧ a ^ 2 = R.index := by
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  -- `e = e₁ e₂` with `e₁² = |H : R|` and `e₂² = pᵏ`
  have hcard : Nat.card H = e ^ 2 * Nat.card Z := card_eq_sq_mul he
  have hHR : Nat.card H = R.index * Nat.card R := by rw [mul_comm, Subgroup.card_mul_index]
  have heq : e ^ 2 = R.index * p ^ k := by
    have : e ^ 2 * Nat.card Z = R.index * p ^ k * Nat.card Z := by
      rw [← hcard, hHR, hRZ]; ring
    exact Nat.eq_of_mul_eq_mul_right hZpos this
  set e₂ := ordProj[p] e with he₂
  set e₁ := ordCompl[p] e with he₁
  have he0 : e ≠ 0 := by
    intro h0; rw [h0] at heq
    have : R.index * p ^ k ≠ 0 := Nat.mul_ne_zero R.index_ne_zero_of_finite (pow_ne_zero _ hp.ne_zero)
    rw [zero_pow two_ne_zero] at heq
    exact this heq.symm
  have hsplit : e₁ * e₂ = e := by rw [he₁, he₂, mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self e p
  have hcop1 : Nat.Coprime e₁ p := (Nat.coprime_ordCompl hp he0).symm
  have hcop12 : Nat.Coprime e₁ e₂ := by
    rw [he₂]; exact Nat.Coprime.pow_right _ hcop1
  have hcopIR : Nat.Coprime R.index (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpR)))
  have he1sq : e₁ ^ 2 = R.index := by
    have h1 : e₁ ^ 2 * e₂ ^ 2 = R.index * p ^ k := by rw [← heq, ← hsplit]; ring
    have hc1 : Nat.Coprime (e₁ ^ 2) (p ^ k) := Nat.Coprime.pow _ _ hcop1
    have hd1 : e₁ ^ 2 ∣ R.index := hc1.dvd_of_dvd_mul_right ⟨e₂ ^ 2, by rw [mul_comm] at h1 ⊢; linarith⟩
    have he2pow : ∃ j, e₂ ^ 2 = p ^ j := ⟨2 * e.factorization p, by rw [he₂, ← pow_mul, mul_comm]⟩
    obtain ⟨j, hj⟩ := he2pow
    have hc2 : Nat.Coprime R.index (e₂ ^ 2) := by
      rw [hj]; exact Nat.Coprime.pow_right _
        ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpR)))
    have hd2 : R.index ∣ e₁ ^ 2 := hc2.dvd_of_dvd_mul_right ⟨p ^ k, by rw [← h1]⟩
    exact Nat.dvd_antisymm hd1 hd2
  have he2sq : e₂ ^ 2 = p ^ k := by
    have h1 : e₁ ^ 2 * e₂ ^ 2 = R.index * p ^ k := by rw [← heq, ← hsplit]; ring
    rw [he1sq] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero R.index_ne_zero_of_finite) h1
  have he2pos : 0 < e₂ := by rw [he₂]; exact pow_pos hp.pos _
  have he1pos : 0 < e₁ := Nat.pos_of_ne_zero (fun h => R.index_ne_zero_of_finite (by
    rw [← he1sq, h]; rfl))
  -- every constituent has multiplicity at least `e₁`
  have hresR := (irr_isNatComb hχ).pull R.subtype
  have hlow : ∀ ζ ∈ Irr R, mult (pull R.subtype χ) ζ ≠ 0 → e₁ ≤ mult (pull R.subtype χ) ζ := by
    intro ζ hζ hne
    set c := mult (pull (Subgroup.inclusion hZR) ζ) θ
    have hc := ((irr_isNatComb hζ).pull (Subgroup.inclusion hZR)).mult_eq hθ
    have h1 := fr_ip_mul_card hχ hθ hres he hZR ζ
    rw [← hresR.mult_eq hζ, ← hc, hRZ] at h1
    have h2 : mult (pull R.subtype χ) ζ * (p ^ k * Nat.card Z) = e * Nat.card Z * c := by
      exact_mod_cast h1
    set a := mult (pull R.subtype χ) ζ
    have h3 : a * p ^ k = e * c := by
      refine Nat.eq_of_mul_eq_mul_right hZpos ?_
      calc a * p ^ k * Nat.card Z = a * (p ^ k * Nat.card Z) := by ring
        _ = e * Nat.card Z * c := h2
        _ = e * c * Nat.card Z := by ring
    have h4 : a * e₂ = e₁ * c := by
      refine Nat.eq_of_mul_eq_mul_right he2pos ?_
      calc a * e₂ * e₂ = a * e₂ ^ 2 := by ring
        _ = a * p ^ k := by rw [he2sq]
        _ = e * c := h3
        _ = e₁ * c * e₂ := by rw [← hsplit]; ring
    have hdvd : e₁ ∣ mult (pull R.subtype χ) ζ := hcop12.dvd_of_dvd_mul_right ⟨c, h4⟩
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  -- the sum of squares of the multiplicities is `|H : R| = e₁²`
  have hss : ∑ ζ ∈ irrFinset R, mult (pull R.subtype χ) ζ ^ 2 = e₁ ^ 2 := by
    have h1 := fr_ip_pull hχ hθ hres he (Subgroup.subtype_injective R)
      (by rw [Subgroup.range_subtype]; exact hZR)
    rw [ip_natComb_self hresR, hHR] at h1
    have : ((∑ ζ ∈ irrFinset R, mult (pull R.subtype χ) ζ ^ 2 : ℕ) : ℂ) * Nat.card R =
        (R.index : ℂ) * Nat.card R := by push_cast at h1 ⊢; rw [h1]
    have hR0 : (Nat.card R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    have := mul_right_cancel₀ hR0 this
    rw [he1sq]; exact_mod_cast this
  -- hence a single constituent
  obtain ⟨ζ, hζ, hne⟩ : ∃ ζ ∈ irrFinset R, mult (pull R.subtype χ) ζ ≠ 0 := by
    by_contra hc; push Not at hc
    rw [Finset.sum_eq_zero fun ζ hζ => by rw [hc ζ hζ]; simp] at hss
    exact absurd hss.symm (by positivity)
  have hζ' := mem_irrFinset.mp hζ
  have hge := hlow ζ hζ' hne
  have hrest := Finset.add_sum_erase (irrFinset R) (fun ζ => mult (pull R.subtype χ) ζ ^ 2) hζ
  rw [hss] at hrest
  have hsq : e₁ ^ 2 ≤ mult (pull R.subtype χ) ζ ^ 2 := Nat.pow_le_pow_left hge 2
  have hothers : ∀ ξ ∈ (irrFinset R).erase ζ, mult (pull R.subtype χ) ξ = 0 := by
    intro ξ hξ
    by_contra hξ0
    have hξ' := mem_irrFinset.mp (Finset.mem_of_mem_erase hξ)
    have h1 := Nat.pow_le_pow_left (hlow ξ hξ' hξ0) 2
    have h2 := Finset.single_le_sum (f := fun ξ => mult (pull R.subtype χ) ξ ^ 2)
      (fun _ _ => Nat.zero_le _) hξ
    have : 0 < e₁ ^ 2 := by positivity
    omega
  have hsum0 : ∑ ξ ∈ (irrFinset R).erase ζ, mult (pull R.subtype χ) ξ ^ 2 = 0 :=
    Finset.sum_eq_zero fun ξ hξ => by rw [hothers ξ hξ]; simp
  have ha : mult (pull R.subtype χ) ζ ^ 2 = e₁ ^ 2 := by omega
  refine ⟨ζ, hζ', mult (pull R.subtype χ) ζ, ?_, by rw [ha, he1sq]⟩
  conv_lhs => rw [hresR.eq_sum]
  rw [← Finset.add_sum_erase _ _ hζ, Finset.sum_eq_zero fun ξ hξ => by rw [hothers ξ hξ]; simp]
  simp

end Triple

end

end CFSGOutside.Gagola
