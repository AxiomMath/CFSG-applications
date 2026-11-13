import CFSGOutside.ChillagSonn.SylowTower

/-!
# Chillag–Sonn: auxiliary group theory for Theorem 1

Odd-order Sylow-metacyclic groups are solvable; basic facts on `O(G)`; normal 2-complements for cyclic Sylow
2-subgroups (Burnside's transfer theorem), so a perfect group with cyclic Sylow 2-subgroups has odd order; normal
subgroups of order 2 are central; automorphisms of cyclic groups commute.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GroupTheory

/-- Solvability of odd-order Sylow-metacyclic groups, by induction on the order. -/
theorem isSolvable_of_odd_aux [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] (n : ℕ) :
    ∀ {G : Type} [Group G] [Finite G], Nat.card G = n → SylowMetacyclic G → Odd n → Group.IsSolvable G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hcard hG hodd
  by_cases h1 : n = 1
  · subst h1; have := (Nat.card_eq_one_iff_unique.mp hcard).1; infer_instance
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpodd : Odd p := hp.odd_of_ne_two fun h => by
    rw [h] at hpn; exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨j, hj⟩ := hpodd; omega
  have hr : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r ≠ p → ¬ r ∣ p - 1 ∧ ¬ r ∣ p + 1 := by
    intro r hr hrN hrp
    rw [hcard] at hrN
    have hpr : p ≤ r := Nat.minFac_le_of_dvd hr.two_le hrN
    obtain ⟨a, ha⟩ := hpodd
    obtain ⟨b, hb⟩ := Odd.of_dvd_nat hodd hrN
    have : p + 1 < r := by omega
    exact ⟨Nat.not_dvd_of_pos_of_lt (by omega) (by omega), Nat.not_dvd_of_pos_of_lt (by omega) this⟩
  obtain ⟨K, hKn, hKcop, k, hk⟩ := exists_normalPComplement_of_metacyclic (G := G) (p := p) (fun P => hG p P) hr
  have hpK : ¬ p ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd hp).1 hKcop.symm
  have hnK : n = Nat.card K * p ^ k := by rw [← hk, Subgroup.card_mul_index, hcard]
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [pow_zero, mul_one] at hnK; exact hpK (by rw [← hnK]; exact hpn)
  have hlt : Nat.card K < n := by
    rw [hnK]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hK0) (Nat.one_lt_pow hk0 hp.one_lt)
  have hoddK : Odd (Nat.card K) := Odd.of_dvd_nat hodd (hnK ▸ dvd_mul_right _ _)
  have : Group.IsSolvable K := ih _ hlt rfl (hG.subgroup K) hoddK
  have := (IsPGroup.of_card (p := p) (G := G ⧸ K) (n := k) (by rw [← Subgroup.index_eq_card, hk])).isNilpotent
  exact Group.isSolvable_of_subgroup_quotient K

/-- An odd-order Sylow-metacyclic group is solvable (it has a Sylow tower). -/
theorem isSolvable_of_odd_of_sylowMetacyclic [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] {G : Type} [Group G] [Finite G] (hG : SylowMetacyclic G)
    (hodd : Odd (Nat.card G)) : Group.IsSolvable G :=
  isSolvable_of_odd_aux _ rfl hG hodd

/-- The join of a normal odd-order subgroup and an odd-order subgroup has odd order. -/
theorem odd_card_sup {G : Type} [Group G] [Finite G] (N₁ N₂ : Subgroup G) [hN₁ : N₁.Normal]
    (h₁ : Odd (Nat.card N₁)) (h₂ : Odd (Nat.card N₂)) : Odd (Nat.card (N₁ ⊔ N₂ : Subgroup G)) := by
  let L : Subgroup G := N₁ ⊔ N₂
  let M : Subgroup L := N₁.subgroupOf L
  have : M.Normal := Subgroup.normal_subgroupOf
  let f : N₂ →* L ⧸ M := (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : N₂ ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N₁) (t := N₂)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN₁.conj_mem' a ha b
  have hM : Nat.card M = Nat.card N₁ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hd : Nat.card L ∣ Nat.card N₁ * Nat.card N₂ := by
    rw [M.card_eq_card_quotient_mul_card_subgroup, hM, mul_comm]
    exact mul_dvd_mul_left _ (Subgroup.card_dvd_of_surjective hf)
  exact Odd.of_dvd_nat (h₁.mul h₂) hd

/-- `O(G)` has odd order. -/
theorem odd_card_oddCore {G : Type} [Group G] [Finite G] : Odd (Nat.card (oddCore G)) := by
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup G => N.Normal ∧ Odd (Nat.card N)) (a := ⊥) ⟨inferInstance, by simp⟩
  have hge : ∀ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) → N ≤ M := by
    rintro N ⟨hN, hNo⟩
    have := hM.1.1
    rw [hM.eq_of_le ⟨Subgroup.sup_normal M N, odd_card_sup M N hM.1.2 hNo⟩ le_sup_left]
    exact le_sup_right
  rw [show oddCore G = M from le_antisymm (sSup_le hge) (le_sSup hM.1)]
  exact hM.1.2

/-- Every normal subgroup of odd order lies in `O(G)`. -/
theorem le_oddCore {G : Type} [Group G] {N : Subgroup G} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ oddCore G :=
  le_sSup ⟨hN, hodd⟩

/-- A cyclic Sylow 2-subgroup has a normal complement (Burnside's transfer theorem). -/
theorem exists_normalTwoComplement_of_isCyclic {G : Type} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : IsCyclic P) : ∃ N : Subgroup G, IsNormalPComplement 2 N := by
  by_cases hodd : Odd (Nat.card G)
  · exact ⟨⊤, inferInstance, by rwa [Subgroup.card_top, Nat.coprime_two_right], 0, by simp⟩
  have hp : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
  have hPc := IsCyclic.normalizer_le_centralizer hp hP
  have hc : (MonoidHom.transferSylow P hPc).ker.IsComplement' P := MonoidHom.ker_transferSylow_isComplement' P hPc
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  refine ⟨_, MonoidHom.normal_ker _, ?_, k, hc.symm.index_eq_card.trans hk⟩
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (MonoidHom.not_dvd_card_ker_transferSylow P hPc)).symm

/-- If the Sylow 2-subgroups of `G` have order at most 2, then `G` has a normal 2-complement. -/
theorem exists_normalTwoComplement_of_card_le_two [FrobeniusNormalPComplement.{0}] {G : Type} [Group G]
    [Finite G] (h : ∀ P : Sylow 2 G, Nat.card P ≤ 2) : ∃ N : Subgroup G, IsNormalPComplement 2 N := by
  let P : Sylow 2 G := default
  refine exists_normalTwoComplement_of_isCyclic P ?_
  rcases (show Nat.card P = 1 ∨ Nat.card P = 2 by have := h P; have : 0 < Nat.card P := Nat.card_pos; omega)
    with h1 | h2
  · have := (Nat.card_eq_one_iff_unique.mp h1).1; infer_instance
  · exact isCyclic_of_prime_card h2

/-- A perfect finite group with a cyclic Sylow 2-subgroup has odd order. -/
theorem odd_card_of_perfect_of_cyclic [FrobeniusNormalPComplement.{0}] {G : Type} [Group G] [Finite G]
    (hperf : commutator G = ⊤) (P : Sylow 2 G) (hP : IsCyclic P) : Odd (Nat.card G) := by
  obtain ⟨N, hNn, hcop, k, hk⟩ := exists_normalTwoComplement_of_isCyclic P hP
  have : Group.IsPerfect G := ⟨hperf⟩
  have := (IsPGroup.of_card (p := 2) (G := G ⧸ N) (n := k) (by rw [← Subgroup.index_eq_card, hk])).isNilpotent
  have : Subsingleton (G ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (G ⧸ N) inferInstance
  have h1 : N.index = 1 := by rw [Subgroup.index_eq_card]; exact Nat.card_unique
  rw [← Subgroup.card_mul_index N, h1, mul_one]
  exact Nat.coprime_two_right.mp hcop

/-- A normal subgroup of order at most 2 is central. -/
theorem le_center_of_card_le_two {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Finite N]
    (h : Nat.card N ≤ 2) : N ≤ Subgroup.center G := by
  classical
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_contra hne
  have hz1 : z ≠ 1 := by rintro rfl; simp at hne
  have hc1 : g * z * g⁻¹ ≠ 1 := by
    intro h'; exact hz1 (by simpa using h')
  have hcz : g * z * g⁻¹ ≠ z := fun h' => hne (mul_inv_eq_iff_eq_mul.mp h')
  have hmem : g * z * g⁻¹ ∈ N := ‹N.Normal›.conj_mem z hz g
  have := Fintype.ofFinite N
  have h3 := Finset.card_le_univ ({⟨1, N.one_mem⟩, ⟨z, hz⟩, ⟨g * z * g⁻¹, hmem⟩} : Finset N)
  rw [Finset.card_eq_three.mpr ⟨_, _, _, fun h' => hz1 (congrArg Subtype.val h').symm,
    fun h' => hc1 (congrArg Subtype.val h').symm, fun h' => hcz (congrArg Subtype.val h').symm, rfl⟩,
    ← Nat.card_eq_fintype_card] at h3
  omega

/-- The automorphisms of a finite cyclic group commute. -/
theorem mulAut_comm_of_isCyclic {S : Type} [Group S] [Finite S] [IsCyclic S] (σ τ : MulAut S) :
    σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := σ.toMonoidHom.map_cyclic
  obtain ⟨n, hn⟩ := τ.toMonoidHom.map_cyclic
  have hm' : ∀ x, σ x = x ^ m := hm
  have hn' : ∀ x, τ x = x ^ n := hn
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply, hm' (τ x), hn' x, hn' (σ x), hm' x, ← zpow_mul, ← zpow_mul, mul_comm]

end CFSGOutside.ChillagSonn
