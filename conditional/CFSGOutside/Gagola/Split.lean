import CFSGOutside.Gagola.Cor36

/-!
# Splitting a fully ramified triple (Gagola, Lemma 2.1(e))

If `(H, Z, χ)` is fully ramified, `Z ≤ K ⊴ H` and `χ_K` has a single irreducible constituent `τ`,
then `(H, K, χ)` and `(K, Z, τ)` are fully ramified triples.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators
open Classical

noncomputable section

variable {H : Type} [Group H] [Fintype H] {Z : Subgroup H} {χ : H → ℂ}

/-- **Gagola, Lemma 2.1(e).** -/
theorem fr_split (hfr : FullyRamified Z χ) (K : Subgroup H) [hK : K.Normal] (hZK : Z ≤ K)
    (huniq : ∀ τ₁ τ₂ : K → ℂ, τ₁ ∈ Irr K → τ₂ ∈ Irr K → mult (pull K.subtype χ) τ₁ ≠ 0 →
      mult (pull K.subtype χ) τ₂ ≠ 0 → τ₁ = τ₂) :
    FullyRamified K χ ∧ ∃ τ : K → ℂ, FullyRamified (Z.subgroupOf K) τ := by
  obtain ⟨hZ, hχ, θ, e, hθ, hres, he⟩ := hfr
  have hχK := (irr_isNatComb hχ).pull K.subtype
  obtain ⟨τ, hτ, hm⟩ := exists_constituent hχK (by
    obtain ⟨d, hd, hd'⟩ := irr_one hχ
    simp only [pull_apply, map_one, hd']
    exact_mod_cast hd.ne')
  set a := mult (pull K.subtype χ) τ with ha
  -- `χ_K = a τ`
  have hχKτ : pull K.subtype χ = (a : ℂ) • τ := by
    conv_lhs => rw [hχK.eq_sum]
    rw [Finset.sum_eq_single τ]
    · intro τ' hτ' hne
      have : mult (pull K.subtype χ) τ' = 0 := by
        by_contra h0; exact hne (huniq τ' τ (mem_irrFinset.mp hτ') hτ h0 hm)
      rw [this, Nat.cast_zero, zero_smul]
    · intro h; exact absurd (mem_irrFinset.mpr hτ) h
  -- `a² = |H : K|`
  have ha2 : a ^ 2 = K.index := by
    have h1 := fr_ip_pull hχ hθ hres he (Subgroup.subtype_injective K)
      (by rw [Subgroup.range_subtype]; exact hZK)
    rw [hχKτ, ip_smul_left, ip_smul_right, ip_irr_self hτ, ← K.card_mul_index] at h1
    have hK0 : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h2 : ((a ^ 2 : ℕ) : ℂ) * Nat.card K = (K.index : ℂ) * Nat.card K := by
      push_cast at h1 ⊢; rw [mul_comm (K.index : ℂ)]; linear_combination h1
    exact_mod_cast mul_right_cancel₀ hK0 h2
  refine ⟨⟨hK, hχ, τ, a, hτ, hχKτ, ha2⟩, τ, ?_⟩
  -- `(K, Z, τ)`
  set ZK := Z.subgroupOf K
  have hZKn : ZK.Normal := hZ.subgroupOf K
  set eZ : ZK ≃* Z := Subgroup.subgroupOfEquivOfLe hZK
  set θK : ZK → ℂ := pull eZ.toMonoidHom θ
  have hθK : θK ∈ Irr ZK := irr_pull_mulEquiv eZ hθ
  have ha0 : a ≠ 0 := hm
  -- `a ∣ e`
  have hidx : Z.index = ZK.index * K.index := (Subgroup.relIndex_mul_index hZK).symm
  have hdvd : a ∣ e := by
    have : a ^ 2 ∣ e ^ 2 := ⟨ZK.index, by rw [he, hidx, ha2, mul_comm]⟩
    exact (Nat.pow_dvd_pow_iff two_ne_zero).mp this
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨hZKn, hτ, θK, b, hθK, ?_, ?_⟩
  · funext z
    have h1 := congrFun hres (eZ z)
    have h2 := congrFun hχKτ (ZK.subtype z)
    simp only [pull_apply, Subgroup.coe_subtype, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    have hz : ((eZ z : Z) : H) = ((z : K) : H) := rfl
    rw [hz, h2, hb] at h1
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
    simp only [θK, pull_apply, MulEquiv.coe_toMonoidHom]
    push_cast at h1
    exact mul_left_cancel₀ ha0' (by linear_combination h1)
  · have h1 : (a * b) ^ 2 = ZK.index * a ^ 2 := by rw [← hb, he, hidx, ha2]
    have ha2pos : 0 < a ^ 2 := by positivity
    have : b ^ 2 * a ^ 2 = ZK.index * a ^ 2 := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right ha2pos this

end

end CFSGOutside.Gagola
