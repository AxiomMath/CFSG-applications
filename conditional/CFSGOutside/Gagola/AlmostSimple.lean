import CFSGOutside.Gagola.Thm25

/-!
# Gagola, Theorem 2.5(a) for almost simple quotients

If `H/K ≅ X0` has a nonabelian simple normal subgroup `S` with trivial centralizer (so `X0` is almost
simple) and `S` has the Sylow structure below, then we get a contradiction.
-/

namespace CFSGOutside.Gagola

open scoped BigOperators Pointwise
open Classical

noncomputable section

/-- A cyclic `q`-subgroup of order `qᵇ` of a group with a core-free subgroup `M` has `qᵇ ≤ [G:M]`. -/
theorem card_le_index_of_coreFree {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hcore : M.normalCore = ⊥) {Q : Subgroup G} [IsCyclic Q] {q b : ℕ} (hq : q.Prime)
    (hb : 0 < b) (hQ : Nat.card Q = q ^ b) : q ^ b ≤ M.index := by
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := Q)
  have hy' : orderOf y = q ^ b := by rw [orderOf_eq_card_of_forall_mem_zpowers hy, hQ]
  have hyG : orderOf (y : G) = q ^ b := by rw [Subgroup.orderOf_coe, hy']
  have hz : (y : G) ^ q ^ (b - 1) ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hyG] at this
    have := Nat.le_of_dvd (pow_pos hq.pos _) this
    have := (Nat.pow_le_pow_iff_right hq.one_lt).mp this
    omega
  obtain ⟨c, hc⟩ : ∃ c : G ⧸ M, (y : G) ^ q ^ (b - 1) • c ≠ c := by
    by_contra hcon
    push Not at hcon
    apply hz
    have hker : (y : G) ^ q ^ (b - 1) ∈ (MulAction.toPermHom G (G ⧸ M)).ker := by
      rw [MonoidHom.mem_ker]
      ext x
      exact hcon x
    rw [← Subgroup.normalCore_eq_ker, hcore] at hker
    exact hker
  set d := Function.minimalPeriod (fun x => (y : G) • x) c
  have hd1 : d ∣ q ^ b := by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← hyG, pow_orderOf_eq_one, one_smul]
  have hd2 : ¬ d ∣ q ^ (b - 1) := by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]; exact hc
  obtain ⟨i, hi, hdi⟩ := (Nat.dvd_prime_pow hq).mp hd1
  have hib : i = b := by
    by_contra hne
    apply hd2
    rw [hdi]
    exact Nat.pow_dvd_pow q (by omega)
  letI := Fintype.ofFinite (G ⧸ M)
  have hle : d ≤ Fintype.card (G ⧸ M) := Function.minimalPeriod_le_card
  rw [hdi, hib] at hle
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact hle

theorem card_le_factorial_index_of_coreFree {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hcore : M.normalCore = ⊥) : Nat.card G ≤ M.index.factorial := by
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  calc Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ M)) := Nat.card_le_card_of_injective _ hinj
    _ = M.index.factorial := by rw [Nat.card_perm]; rfl

section Sylow

variable {X0 : Type} [Group X0] [Finite X0] (S : Subgroup X0) [S.Normal] [IsSimpleGroup S]

theorem sylow_data
    (hC : Subgroup.centralizer (S : Set X0) = ⊥)
    (hex : ∀ (r : ℕ) [Fact r.Prime] (R : Sylow r X0), IsCyclic (R : Subgroup X0) →
      ∃ M : Subgroup X0, M.index = Nat.card R)
    {r : ℕ} [hr : Fact r.Prime] (hrS : ¬ r ∣ S.index) (P : Sylow r S)
    (hc : IsCyclic (P : Subgroup S)) (h1 : Nat.card P ≠ 1) :
    ∃ (M A : Subgroup X0), M.normalCore = ⊥ ∧ M.index = Nat.card P ∧ IsCyclic A ∧
      Nat.card A = Nat.card P := by
  set A : Subgroup X0 := (P : Subgroup S).map S.subtype with hA
  have hAc : Nat.card A = Nat.card P :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective S)
  have hAcyc : IsCyclic A :=
    isCyclic_of_surjective (S.subtype.subgroupMap (P : Subgroup S)) (S.subtype.subgroupMap_surjective _)
  have hcard : Nat.card A = r ^ (Nat.card X0).factorization r := by
    rw [hAc, Sylow.card_eq_multiplicity, ← S.card_mul_index,
      Nat.factorization_mul Nat.card_pos.ne' (Subgroup.index_ne_zero_of_finite),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hrS, add_zero]
  let R : Sylow r X0 := Sylow.ofCard A hcard
  obtain ⟨M, hM⟩ := hex r R hAcyc
  have hM' : M.index = Nat.card P := by rw [hM]; exact hAc
  refine ⟨M, A, ?_, hM', hAcyc, hAc⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h1 (by rw [ha, h, pow_zero]))
  have hNn : (M.normalCore).Normal := M.normalCore_normal
  rcases (inferInstance : ((M.normalCore).subgroupOf S).Normal).eq_bot_or_eq_top with hb | ht
  · rw [← le_bot_iff, ← hC]
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hcS : s * n * s⁻¹ * n⁻¹ ∈ S := by
      have : s * n * s⁻¹ * n⁻¹ = s * (n * s⁻¹ * n⁻¹) := by group
      rw [this]
      exact S.mul_mem hs (Subgroup.Normal.conj_mem inferInstance _ (S.inv_mem hs) n)
    have hcN : s * n * s⁻¹ * n⁻¹ ∈ M.normalCore :=
      M.normalCore.mul_mem (Subgroup.Normal.conj_mem hNn n hn s) (M.normalCore.inv_mem hn)
    have : (⟨_, hcS⟩ : S) ∈ (M.normalCore).subgroupOf S := hcN
    rw [hb, Subgroup.mem_bot] at this
    have h2 : s * n * s⁻¹ * n⁻¹ = 1 := congrArg Subtype.val this
    have h3 : s * n * s⁻¹ = n := by
      have := congrArg (· * n) h2
      simpa [mul_assoc] using this
    calc s * n = s * n * s⁻¹ * s := by group
      _ = n * s := by rw [h3]
  · exfalso
    have hSN : S ≤ M.normalCore := by
      intro x hx
      have : (⟨x, hx⟩ : S) ∈ (M.normalCore).subgroupOf S := by rw [ht]; trivial
      exact this
    have hSM : S ≤ M := hSN.trans M.normalCore_le
    have := Subgroup.index_dvd_of_le hSM
    rw [hM', ha] at this
    exact hrS ((dvd_pow_self r ha0.ne').trans this)

theorem almost_simple_false_aux
    (hnonab : Nonempty S) (hC : Subgroup.centralizer (S : Set X0) = ⊥)
    (hex : ∀ (r : ℕ) [Fact r.Prime] (R : Sylow r X0), IsCyclic (R : Subgroup X0) →
      ∃ M : Subgroup X0, M.index = Nat.card R)
    (h : (∃ r₁ r₂ : ℕ, ∃ _ : Fact r₁.Prime, ∃ _ : Fact r₂.Prime, r₁ ≠ r₂ ∧
            ¬ r₁ ∣ S.index ∧ ¬ r₂ ∣ S.index ∧
            (∀ P : Sylow r₁ S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1) ∧
            (∀ P : Sylow r₂ S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1)) ∨
         (∃ r : ℕ, ∃ _ : Fact r.Prime, ¬ r ∣ S.index ∧
            (∀ P : Sylow r S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1 ∧
              (Nat.card P).factorial < Nat.card S))) :
    False := by
  rcases h with ⟨r₁, r₂, hr₁, hr₂, hne, hi₁, hi₂, h₁, h₂⟩ | ⟨r, hr, hi, hP⟩
  · obtain ⟨P₁⟩ := (inferInstance : Nonempty (Sylow r₁ S))
    obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow r₂ S))
    obtain ⟨M₁, A₁, hM₁, hI₁, hA₁, hc₁⟩ := sylow_data S hC hex hi₁ P₁ (h₁ P₁).1 (h₁ P₁).2
    obtain ⟨M₂, A₂, hM₂, hI₂, hA₂, hc₂⟩ := sylow_data S hC hex hi₂ P₂ (h₂ P₂).1 (h₂ P₂).2
    obtain ⟨a, ha⟩ := P₁.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := P₂.isPGroup'.exists_card_eq
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => (h₁ P₁).2 (by rw [ha, h, pow_zero]))
    have hb0 : 0 < b := Nat.pos_of_ne_zero (fun h => (h₂ P₂).2 (by rw [hb, h, pow_zero]))
    have e1 := card_le_index_of_coreFree hM₁ (Q := A₂) hr₂.out hb0 (hc₂.trans hb)
    have e2 := card_le_index_of_coreFree hM₂ (Q := A₁) hr₁.out ha0 (hc₁.trans ha)
    rw [hI₁, ha] at e1
    rw [hI₂, hb] at e2
    have heq : r₁ ^ a = r₂ ^ b := le_antisymm e2 e1
    have : r₁ ∣ r₂ ^ b := heq ▸ dvd_pow_self r₁ ha0.ne'
    exact hne ((Nat.prime_dvd_prime_iff_eq hr₁.out hr₂.out).mp (hr₁.out.dvd_of_dvd_pow this))
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r S))
    obtain ⟨M, A, hM, hI, -, -⟩ := sylow_data S hC hex hi P (hP P).1 (hP P).2.1
    have h1 := card_le_factorial_index_of_coreFree hM
    rw [hI] at h1
    have h2 : Nat.card S ≤ Nat.card X0 := Subgroup.card_le_card_group S
    have := (hP P).2.2
    omega

end Sylow

theorem almost_simple_false {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) {X0 : Type} [Group X0] [Finite X0] (φ : H →* X0)
    (hφ : Function.Surjective φ) (hZ : Z ≤ φ.ker) (S : Subgroup X0) [S.Normal] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hC : Subgroup.centralizer (S : Set X0) = ⊥)
    (h : (∃ r₁ r₂ : ℕ, ∃ _ : Fact r₁.Prime, ∃ _ : Fact r₂.Prime, r₁ ≠ r₂ ∧
            ¬ r₁ ∣ S.index ∧ ¬ r₂ ∣ S.index ∧
            (∀ P : Sylow r₁ S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1) ∧
            (∀ P : Sylow r₂ S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1)) ∨
         (∃ r : ℕ, ∃ _ : Fact r.Prime, ¬ r ∣ S.index ∧
            (∀ P : Sylow r S, IsCyclic (P : Subgroup S) ∧ Nat.card P ≠ 1 ∧
              (Nat.card P).factorial < Nat.card S))) :
    False := by
  obtain ⟨-, hχ, θ, e, hθ, hres, he⟩ := hfr
  let K := φ.ker
  let eq : H ⧸ K ≃* X0 := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hex : ∀ (r : ℕ) [Fact r.Prime] (R : Sylow r X0), IsCyclic (R : Subgroup X0) →
      ∃ M : Subgroup X0, M.index = Nat.card R := by
    intro r _ R hR
    let R' : Sylow r (H ⧸ K) := R.mapSurjective (f := eq.symm.toMonoidHom) eq.symm.surjective
    have hR' : (R' : Subgroup (H ⧸ K)) = (R : Subgroup X0).map eq.symm.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    have hcyc : IsCyclic (R' : Subgroup (H ⧸ K)) := by
      rw [hR']
      exact isCyclic_of_surjective (eq.symm.toMonoidHom.subgroupMap (R : Subgroup X0))
        (eq.symm.toMonoidHom.subgroupMap_surjective _)
    obtain ⟨M', hM'⟩ := thm_2_5 hχ hθ hres he K hZ R' hcyc
    refine ⟨M'.map eq.toMonoidHom, ?_⟩
    have hc : Nat.card R' = Nat.card R := by
      show Nat.card (R' : Subgroup (H ⧸ K)) = _
      rw [hR']
      exact Subgroup.card_map_of_injective eq.symm.injective
    rw [← hc, ← hM']
    exact Subgroup.index_map_equiv M' eq
  obtain ⟨a, b, hab⟩ := hnonab
  haveI : Nonempty S := ⟨a⟩
  exact almost_simple_false_aux S ⟨a⟩ hC hex h


end

end CFSGOutside.Gagola
