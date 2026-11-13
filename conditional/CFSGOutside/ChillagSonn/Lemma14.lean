import CFSGOutside.Corpus.SolvableHall
import CFSGOutside.ChillagSonn.PNilpotent

/-!
# Lemma (1.4): solvable groups with metacyclic Sylow 2- and 3-subgroups

A finite solvable group `G` whose Sylow 2- and 3-subgroups are metacyclic has a normal `{2,3}`-complement `N`, with
a Hall `{2,3}`-subgroup `A` as complement.

As in the paper: a Hall `2'`-subgroup `X` has a normal 3-complement `C` and a Hall `3'`-subgroup `Y` has a normal
2-complement `B` (`exists_normalPComplement_of_metacyclic`). Both are Hall `{2,3}'`-subgroups of `G`, hence
conjugate, so `N_G(C)` has index dividing both `|G : X|` (a power of 2) and `|G : Y|` (a power of 3): `C ⊴ G`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GroupTheory

variable {G : Type} [Group G] [Finite G]

private lemma mem_of_isPiNumber {π : Set ℕ} {n p : ℕ} (h : FeitThompson.IsPiNumber π n) (hn : n ≠ 0)
    (hp : p.Prime) (hd : p ∣ n) : p ∈ π :=
  h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)

private lemma eq_one_of_forall_prime {n : ℕ} (h : ∀ r, r.Prime → r ∣ n → False) : n = 1 := by
  by_contra hn
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd hn
  exact h r hr hd

private lemma not_dvd_of_le_four {r n : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) (hn : 0 < n) (h4 : n ≤ 4) :
    ¬ r ∣ n := fun h ↦ by
  have : r ≤ 4 := (Nat.le_of_dvd hn h).trans h4
  have := hr.two_le
  interval_cases r <;> first | omega | norm_num at hr

private lemma eq_two_pow_mul_three_pow {n : ℕ} (hn : n ≠ 0) (h : ∀ r, r.Prime → r ∣ n → r = 2 ∨ r = 3) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have hs : n.factorization.support ⊆ {2, 3} := fun r hr ↦ by
    rw [Nat.support_factorization] at hr
    simpa using h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ ↦ pow_zero _), Finset.prod_pair (by norm_num)]

/-- If the Sylow `p`-subgroups of `G` are metacyclic, so are those of every subgroup. -/
theorem isMetacyclic_sylow_subgroup {p : ℕ} [Fact p.Prime] (h : ∀ P : Sylow p G, IsMetacyclic P)
    (H : Subgroup G) (P : Sylow p H) : IsMetacyclic P := by
  obtain ⟨S, hS⟩ := (P.2.map H.subtype).exists_le_sylow
  exact ((h S).of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)).of_mulEquiv
    (P.1.equivMapOfInjective H.subtype H.subtype_injective).symm

/-- A normal `p`-complement `K` of a Hall `q'`-subgroup `H`, viewed in `G`, is normalized by `H`, has order prime
to `p` and `q`, and has `{p, q}`-index. -/
private lemma map_normalPComplement {p q : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hH : FeitThompson.IsHallSubgroup {r | r ≠ q} H) (K : Subgroup H) (hK : IsNormalPComplement p K) :
    H ≤ Subgroup.normalizer (K.map H.subtype : Set G) ∧
      (∀ r, r.Prime → r ∣ Nat.card (K.map H.subtype) → r ≠ p ∧ r ≠ q) ∧
      (∀ r, r.Prime → r ∣ (K.map H.subtype).index → r = p ∨ r = q) := by
  obtain ⟨hKn, hKc, k, hk⟩ := hK
  refine ⟨?_, fun r hr hd ↦ ?_, fun r hr hd ↦ ?_⟩
  · have : ((K.map H.subtype).subgroupOf H).Normal := by
      rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le K)
  · rw [Subgroup.card_map_of_injective H.subtype_injective] at hd
    refine ⟨?_, mem_of_isPiNumber hH.natCard Nat.card_pos.ne' hr (hd.trans (Subgroup.card_subgroup_dvd_card K))⟩
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp hKc.symm hd
  · rw [Subgroup.index_map_subtype, hk] at hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
    · exact .inr (not_not.mp (mem_of_isPiNumber hH.index H.index_ne_zero_of_finite hr h))

/-- **Chillag–Sonn, Lemma (1.4).** A finite solvable group whose Sylow 2- and 3-subgroups are metacyclic has a
normal subgroup `N` of order prime to 6 with a Hall complement `A` of order `2ᵃ3ᵇ`. -/
theorem lemma_1_4 [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] [SolvableHallExistence.{0}] [SolvableHallConjugacy.{0}] {G : Type}
    [Group G] [Finite G] [Group.IsSolvable G] (h2 : ∀ P : Sylow 2 G, IsMetacyclic P)
    (h3 : ∀ P : Sylow 3 G, IsMetacyclic P) :
    ∃ N A : Subgroup G, N.Normal ∧ N ⊓ A = ⊥ ∧ N ⊔ A = ⊤ ∧ Nat.Coprime (Nat.card N) 6 ∧
      (∃ a b : ℕ, Nat.card A = 2 ^ a * 3 ^ b) ∧ Nat.Coprime (Nat.card A) A.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hX⟩ := SolvableHallExistence.exists_isHallSubgroup (X := G) {r | r ≠ 2}
  obtain ⟨Y, hY⟩ := SolvableHallExistence.exists_isHallSubgroup (X := G) {r | r ≠ 3}
  obtain ⟨A, hA⟩ := SolvableHallExistence.exists_isHallSubgroup (X := G) {r | r = 2 ∨ r = 3}
  obtain ⟨C, hC⟩ := exists_normalPComplement_of_metacyclic (G := X) (p := 3) (isMetacyclic_sylow_subgroup h3 X)
    fun r hr hd hr3 ↦ by
      have hr2 := mem_of_isPiNumber hX.natCard Nat.card_pos.ne' hr hd
      exact ⟨not_dvd_of_le_four hr hr2 hr3 (by norm_num) (by norm_num),
        not_dvd_of_le_four hr hr2 hr3 (by norm_num) (by norm_num)⟩
  obtain ⟨B, hB⟩ := exists_normalPComplement_of_metacyclic (G := Y) (p := 2) (isMetacyclic_sylow_subgroup h2 Y)
    fun r hr hd hr2 ↦ by
      have hr3 := mem_of_isPiNumber hY.natCard Nat.card_pos.ne' hr hd
      exact ⟨not_dvd_of_le_four hr hr2 hr3 (by norm_num) (by norm_num),
        not_dvd_of_le_four hr hr2 hr3 (by norm_num) (by norm_num)⟩
  obtain ⟨hXN, hNc, hNi⟩ := map_normalPComplement Nat.prime_three X hX C hC
  obtain ⟨hYM, hMc, hMi⟩ := map_normalPComplement Nat.prime_two Y hY B hB
  set N := C.map X.subtype
  set M := B.map Y.subtype
  let π : Set Nat.Primes := {r | r.val ≠ 2 ∧ r.val ≠ 3}
  have hNπ : IsHallSubgroup π N :=
    ⟨fun r hd ↦ (hNc r.1 r.2 hd).symm, fun r hd h ↦ (hNi r.1 r.2 hd).elim h.2 h.1⟩
  have hMπ : IsHallSubgroup π M :=
    ⟨fun r hd ↦ hMc r.1 r.2 hd, fun r hd h ↦ (hMi r.1 r.2 hd).elim h.1 h.2⟩
  obtain ⟨g, hg⟩ := SolvableHallConjugacy.exists_conj_eq_of_isHallSubgroup_of_solvable inferInstance hNπ hMπ
  have hNn : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one]
    refine eq_one_of_forall_prime fun r hr hd ↦ ?_
    have hdM : r ∣ (Subgroup.normalizer (M : Set G)).index := by
      rwa [hg, ← Subgroup.map_equiv_normalizer_eq,
        Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
    have h2' := not_not.mp (mem_of_isPiNumber hX.index X.index_ne_zero_of_finite hr
      (hd.trans (Subgroup.index_dvd_of_le hXN)))
    have h3' := not_not.mp (mem_of_isPiNumber hY.index Y.index_ne_zero_of_finite hr
      (hdM.trans (Subgroup.index_dvd_of_le hYM)))
    omega
  have hAc r (hr : r.Prime) (hd : r ∣ Nat.card A) : r = 2 ∨ r = 3 :=
    mem_of_isPiNumber hA.natCard Nat.card_pos.ne' hr hd
  have hAi r (hr : r.Prime) (hd : r ∣ A.index) : ¬ (r = 2 ∨ r = 3) :=
    mem_of_isPiNumber hA.index A.index_ne_zero_of_finite hr hd
  have hNA : Nat.Coprime (Nat.card N) (Nat.card A) :=
    Nat.coprime_of_dvd fun r hr h1 h2 ↦ by have := hNc r hr h1; have := hAc r hr h2; omega
  refine ⟨N, A, hNn, Subgroup.inf_eq_bot_of_coprime hNA, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.index_eq_one]
    refine eq_one_of_forall_prime fun r hr hd ↦ hAi r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_right)) ?_
    have := hNi r hr (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
    omega
  · refine Nat.coprime_of_dvd fun r hr h1 h6 ↦ ?_
    have := hNc r hr h1
    rcases (Nat.Prime.dvd_mul hr).mp (show r ∣ 2 * 3 from h6) with h | h <;>
      exact not_dvd_of_le_four hr this.2 this.1 (by norm_num) (by norm_num) h
  · exact ⟨_, _, eq_two_pow_mul_three_pow Nat.card_pos.ne' hAc⟩
  · exact Nat.coprime_of_dvd fun r hr h1 h2 ↦ hAi r hr h2 (hAc r hr h1)

end CFSGOutside.ChillagSonn
