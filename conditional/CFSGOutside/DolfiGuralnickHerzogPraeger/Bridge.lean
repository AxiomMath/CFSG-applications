import CFSGOutside.DolfiGuralnickHerzogPraeger.Defs

/-!
# From the hypotheses of Lemma 4.3 to the properties used in the proof

* a cyclic Sylow `r`-subgroup makes every `r`-subgroup cyclic;
* if *some* subgroup of order `r` has automizer of order prime to `p`, then (Sylow `r`-subgroups
  being cyclic, all subgroups of order `r` are conjugate) every element of order `p` normalizing a
  subgroup of order `r` centralizes it.
-/

namespace CFSGOutside.DolfiGuralnickHerzogPraeger

open Pointwise

lemma isCyclic_of_le_cyclic {G : Type*} [Group G] (S Q : Subgroup G) [IsCyclic S] (h : Q ≤ S) :
    IsCyclic Q := by
  haveI : IsCyclic (Q.subgroupOf S) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe h).surjective

lemma eq_of_card_eq_of_cyclic {S : Type*} [Group S] [Finite S] [IsCyclic S] (A B : Subgroup S)
    (n : ℕ) (hn : 0 < n) (hA : Nat.card A = n) (hB : Nat.card B = n) : A = B := by
  classical
  haveI := Fintype.ofFinite S
  have hT : {x : S | x ^ n = 1}.ncard ≤ n := by
    have := IsCyclic.card_pow_eq_one_le (α := S) hn
    rw [Set.ncard_eq_toFinset_card']
    simpa using this
  have hsub : ∀ C : Subgroup S, Nat.card C = n → (C : Set S) ⊆ {x : S | x ^ n = 1} := by
    intro C hC x hx
    have := pow_card_eq_one' (G := C) (x := ⟨x, hx⟩)
    rw [hC] at this
    have h3 := congrArg Subtype.val this
    simpa using h3
  have hfin : {x : S | x ^ n = 1}.Finite := Set.toFinite _
  have hAeq := Set.eq_of_subset_of_ncard_le (hsub A hA) (by
    have : ((A : Subgroup S) : Set S).ncard = n := by rw [← Nat.card_coe_set_eq]; exact hA
    rw [this]; exact hT) hfin
  have hBeq := Set.eq_of_subset_of_ncard_le (hsub B hB) (by
    have : ((B : Subgroup S) : Set S).ncard = n := by rw [← Nat.card_coe_set_eq]; exact hB
    rw [this]; exact hT) hfin
  exact SetLike.coe_injective (hAeq.trans hBeq.symm)

lemma eq_of_card_eq_of_le_cyclic {G : Type*} [Group G] [Finite G] (S A B : Subgroup G)
    [IsCyclic S] (hA : A ≤ S) (hB : B ≤ S) (n : ℕ) (hn : 0 < n) (hAn : Nat.card A = n)
    (hBn : Nat.card B = n) : A = B := by
  have e := eq_of_card_eq_of_cyclic (A.subgroupOf S) (B.subgroupOf S) n hn
    (by rw [← hAn]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv)
    (by rw [← hBn]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv)
  ext x
  constructor
  · intro hx
    have : (⟨x, hA hx⟩ : S) ∈ A.subgroupOf S := hx
    rw [e] at this
    exact this
  · intro hx
    have : (⟨x, hB hx⟩ : S) ∈ B.subgroupOf S := hx
    rw [← e] at this
    exact this

theorem isCyclic_of_isPGroup {r : ℕ} [Fact r.Prime] {G : Type*} [Group G] [Finite G]
    (h : ∃ R : Sylow r G, IsCyclic R) (Q : Subgroup G) (hQ : IsPGroup r Q) : IsCyclic Q := by
  obtain ⟨R, hR⟩ := h
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S R
  have hcoe : ((g • S : Sylow r G) : Subgroup G) = MulAut.conj g • (S : Subgroup G) :=
    by
    apply SetLike.coe_injective
    rw [Subgroup.coe_pointwise_smul]
    exact Sylow.coe_smul
  have key : ∀ T : Subgroup G, T = MulAut.conj g • (S : Subgroup G) → IsCyclic T →
      IsCyclic (S : Subgroup G) := by
    rintro T rfl hT
    exact isCyclic_of_surjective (Subgroup.equivSMul (MulAut.conj g) (S : Subgroup G)).symm.toMonoidHom
      (Subgroup.equivSMul (MulAut.conj g) (S : Subgroup G)).symm.surjective
  haveI : IsCyclic (S : Subgroup G) := by
    refine key (R : Subgroup G) ?_ hR
    rw [← hcoe, hg]
  exact isCyclic_of_le_cyclic (S : Subgroup G) Q hS

lemma automizerOrder_smul {G : Type*} [Group G] (R : Subgroup G) (c : G) :
    automizerOrder (MulAut.conj c • R) = automizerOrder R := by
  have hf : ∀ K : Subgroup G, MulAut.conj c • K = K.map (MulAut.conj c).toMonoidHom :=
    fun K => rfl
  have hN : Subgroup.normalizer ((MulAut.conj c • R : Subgroup G) : Set G) =
      (Subgroup.normalizer (R : Set G)).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [hf, Subgroup.mem_map_equiv, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro H k
      have := H (c * k * c⁻¹)
      have e1 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
      have e2 : c⁻¹ * (x * (c * k * c⁻¹) * x⁻¹) * c = (c⁻¹ * x * c) * k * (c⁻¹ * x * c)⁻¹ := by
        group
      rw [e1, e2] at this
      exact this
    · intro H h
      have := H (c⁻¹ * h * c)
      have e2 : c⁻¹ * (x * h * x⁻¹) * c = (c⁻¹ * x * c) * (c⁻¹ * h * c) * (c⁻¹ * x * c)⁻¹ := by
        group
      rw [e2]
      exact this
  have hC : Subgroup.centralizer ((MulAut.conj c • R : Subgroup G) : Set G) =
      (Subgroup.centralizer (R : Set G)).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [hf, Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro H k hk
      have := H (c * k * c⁻¹) (by
        have e1 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
        rw [e1]; exact hk)
      have e : c⁻¹ * x * c * k = k * (c⁻¹ * x * c) := by
        have h2 : c⁻¹ * (x * (c * k * c⁻¹)) * c = c⁻¹ * ((c * k * c⁻¹) * x) * c := by rw [this]
        calc c⁻¹ * x * c * k = c⁻¹ * (x * (c * k * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * k * c⁻¹) * x) * c := h2
          _ = k * (c⁻¹ * x * c) := by group
      exact e.symm
    · intro H h hh
      have := H (c⁻¹ * h * c) hh
      calc h * x = c * ((c⁻¹ * h * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * x * c) * (c⁻¹ * h * c)) * c⁻¹ := by rw [this]
        _ = x * h := by group
  unfold automizerOrder
  rw [hN, hC]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective

theorem mem_centralizer_of_automizer {p r : ℕ} [Fact p.Prime] [Fact r.Prime] {G : Type*} [Group G]
    [Finite G] (hcyc : ∃ R : Sylow r G, IsCyclic R)
    (haut : ∃ R : Subgroup G, Nat.card R = r ∧ ¬ p ∣ automizerOrder R)
    (R : Subgroup G) (hR : Nat.card R = r) (g : G) (hg : g ∈ Subgroup.normalizer (R : Set G))
    (hgp : orderOf g = p) : g ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨R0, hR0c, hR0p⟩ := haut
  have hpg : ∀ K : Subgroup G, Nat.card K = r → IsPGroup r K := fun K hK =>
    IsPGroup.of_card (n := 1) (by rw [hK, pow_one])
  obtain ⟨S0, hS0⟩ := (hpg R0 hR0c).exists_le_sylow
  obtain ⟨S1, hS1⟩ := (hpg R hR).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S0 S1
  have hcoe : ((h • S0 : Sylow r G) : Subgroup G) = MulAut.conj h • (S0 : Subgroup G) :=
    by
    apply SetLike.coe_injective
    rw [Subgroup.coe_pointwise_smul]
    exact Sylow.coe_smul
  have hR1 : MulAut.conj h • R0 ≤ (S1 : Subgroup G) := by
    rw [← hh, hcoe]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).2 hS0
  haveI : IsCyclic (S1 : Subgroup G) := isCyclic_of_isPGroup hcyc _ S1.2
  have hcard1 : Nat.card (MulAut.conj h • R0 : Subgroup G) = r := by
    rw [← hR0c]
    exact Nat.card_congr (Subgroup.equivSMul (MulAut.conj h) R0).symm.toEquiv
  have hRe : R = MulAut.conj h • R0 :=
    eq_of_card_eq_of_le_cyclic (S1 : Subgroup G) R _ hS1 hR1 r (Fact.out : r.Prime).pos hR hcard1
  have hnot : ¬ p ∣ automizerOrder R := by
    rw [hRe, automizerOrder_smul]; exact hR0p
  haveI : ((Subgroup.centralizer (R : Set G)).subgroupOf (Subgroup.normalizer (R : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer _
  set N := Subgroup.normalizer (R : Set G) with hN
  set C := (Subgroup.centralizer (R : Set G)).subgroupOf N with hC
  let gh : N := ⟨g, hg⟩
  have hgh : gh ^ p = 1 := by
    apply Subtype.ext
    simp [gh, ← hgp, pow_orderOf_eq_one]
  have hm : C.index = automizerOrder R := rfl
  have h1 : gh ^ C.index ∈ C := Subgroup.pow_index_mem C gh
  have h2 : gh ^ p ∈ C := by rw [hgh]; exact C.one_mem
  have hcop : Nat.Coprime p C.index := by
    rw [hm]; exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hnot
  have hb : (1 : ℤ) = (p : ℤ) * Nat.gcdA p C.index + (C.index : ℤ) * Nat.gcdB p C.index := by
    have := Nat.gcd_eq_gcd_ab p C.index
    rw [hcop.gcd_eq_one] at this
    simpa using this
  have hmem : gh ∈ C := by
    have : gh = (gh ^ p) ^ (Nat.gcdA p C.index) * (gh ^ C.index) ^ (Nat.gcdB p C.index) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb, zpow_one]
    rw [this]
    exact C.mul_mem (C.zpow_mem h2 _) (C.zpow_mem h1 _)
  exact hmem

end CFSGOutside.DolfiGuralnickHerzogPraeger
