import CFSGOutside.Gagola.Main

/-!
# Auxiliary group theory for Gagola's Theorem 4.5 (perfect case)

* a nonabelian Sylow 2-subgroup has order at least 8;
* Sylow 2-subgroups of `H/Z` map onto Sylow 2-subgroups of `H/K`;
* an element of order 8 in the image of a group of order 16 comes from an element of order 8.
-/

namespace CFSGOutside.Gagola

open Classical

noncomputable section

/-- A nonabelian Sylow 2-subgroup has order `2 ^ n` with `3 ≤ n`. -/
theorem sylow_two_nonabelian_card {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (h : ¬ IsMulCommutative (S : Subgroup X)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nat.card S = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(Nat.card X).factorization 2, ?_, Sylow.card_eq_multiplicity S⟩
  by_contra hn
  push Not at hn
  apply h
  have hc := Sylow.card_eq_multiplicity S
  generalize (Nat.card X).factorization 2 = n at hn hc
  interval_cases n
  · have : Nat.card S = 1 := by simpa using hc
    haveI : Subsingleton S := (Nat.card_eq_one_iff_unique.mp this).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have hc2 : Nat.card S = 2 := by simpa using hc
    haveI : Fact (Nat.Prime (Nat.card S)) := ⟨by rw [hc2]; exact Nat.prime_two⟩
    haveI : IsCyclic S := isCyclic_of_prime_card (p := Nat.card S) rfl
    letI := IsCyclic.commGroup (α := S)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hc)

/-- The quotient map `H/Z → H/K` for `Z ≤ K`. -/
def quotMap {H : Type*} [Group H] (Z K : Subgroup H) [Z.Normal] [K.Normal] (hZK : Z ≤ K) :
    H ⧸ Z →* H ⧸ K :=
  QuotientGroup.map Z K (MonoidHom.id H) (by simpa using hZK)

theorem quotMap_surjective {H : Type*} [Group H] (Z K : Subgroup H) [Z.Normal] [K.Normal]
    (hZK : Z ≤ K) : Function.Surjective (quotMap Z K hZK) := by
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨(h : H ⧸ Z), rfl⟩

/-- An element of order `8` in a group of order `16` containing an element whose order is a multiple of `8`. -/
theorem exists_orderOf_eight {G : Type*} [Group G] (P : Subgroup G) (hP : Nat.card P = 16) {y : G}
    (hy : y ∈ P) (h8 : 8 ∣ orderOf y) : ∃ z ∈ P, orderOf z = 8 := by
  have hdvd : orderOf y ∣ 16 := by
    have h1 : orderOf y = orderOf (⟨y, hy⟩ : P) := Subgroup.orderOf_coe (⟨y, hy⟩ : P)
    rw [← hP, h1]
    exact orderOf_dvd_natCard _
  have hpos : 0 < orderOf y := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf y ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have : orderOf y = 8 ∨ orderOf y = 16 := by omega
  rcases this with h | h
  · exact ⟨y, hy, h⟩
  · refine ⟨y ^ 2, P.pow_mem hy 2, ?_⟩
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]

end

end CFSGOutside.Gagola
