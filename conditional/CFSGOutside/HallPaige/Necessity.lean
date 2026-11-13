import CFSGOutside.HallPaige.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Necessity of the Hall–Paige condition

Hall–Paige (1955), Theorem 5: if a finite group `G` has a complete mapping, then its Sylow
2-subgroups are trivial or non-cyclic.

Proof: if `P` is a nontrivial cyclic Sylow 2-subgroup, the transfer `φ : G →* P` is surjective with
kernel a normal 2-complement (`IsCyclic.isComplement'`, Burnside). For any multiplicative map `f`
to a commutative group and any complete mapping `θ`, comparing the products of `f (x * θ x)`
and of `f x` gives `∏ g, f g = 1`. For `f = φ`, however, `∏ g, φ g = (∏ a : P, a) ^ |G : P|`,
which is the involution of `P`, raised to an odd power.
-/

namespace CFSGOutside.HallPaige

open Finset

section Lemmas

variable {G A : Type*} [Group G] [CommGroup A]

/-- If `G` has a complete mapping, the product of the values of a homomorphism `G →* A` into a
commutative group is trivial. -/
theorem prod_eq_one_of_isCompleteMapping [Fintype G] (f : G →* A) {θ : G → G}
    (hθ : IsCompleteMapping θ) : ∏ g, f g = 1 := by
  have h1 : ∏ x, f (x * θ x) = ∏ g, f g :=
    Fintype.prod_bijective _ hθ.2 _ _ fun _ => rfl
  have h2 : ∏ x, f (θ x) = ∏ g, f g :=
    Fintype.prod_bijective _ hθ.1 _ _ fun _ => rfl
  simp only [map_mul, prod_mul_distrib, h2] at h1
  simpa using h1

/-- For a surjective homomorphism `f : G →* A`, the product of its values is the product of all
elements of `A`, raised to the common fibre size `c`, where `c * |A| = |G|`. -/
theorem exists_prod_eq_pow_of_surjective [Fintype G] [Fintype A] [DecidableEq A] (f : G →* A)
    (hf : Function.Surjective f) :
    ∃ c : ℕ, c * Nat.card A = Nat.card G ∧ ∏ g, f g = (∏ a, a) ^ c := by
  have hfib : ∀ a : A, #{g | f g = a} = #{g | f g = 1} := fun a =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf a) (hf 1)
  refine ⟨#{g | f g = 1}, ?_, ?_⟩
  · have h := card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) fun _ _ => mem_univ _
    rw [sum_congr rfl fun a _ => hfib a, sum_const, card_univ, card_univ, smul_eq_mul] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h, mul_comm]
  · rw [← prod_fiberwise univ f (fun g => f g), ← prod_pow]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_congr rfl (g := fun _ => a) (fun g hg => (mem_filter.mp hg).2), prod_const, hfib]

/-- In a cyclic group of even order, the product of all elements, raised to an odd power, is
nontrivial. -/
theorem prod_univ_pow_ne_one [Fintype A] [IsCyclic A] (heven : Even (Nat.card A)) {k : ℕ}
    (hk : Odd k) : (∏ a : A, a) ^ k ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  set n := Nat.card A with hn
  have hn0 : 0 < n := Nat.card_pos
  have hinj : Function.Injective fun i : Fin n => g ^ (i : ℕ) := by
    intro i j hij
    have := pow_injOn_Iio_orderOf (x := g) (by simp [hg, i.2]) (by simp [hg, j.2]) hij
    exact Fin.ext this
  have hbij : Function.Bijective fun i : Fin n => g ^ (i : ℕ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [hn, Nat.card_eq_fintype_card]⟩
  have hprod : ∏ a : A, a = g ^ (∑ i ∈ range n, i) := by
    rw [← Fintype.prod_bijective _ hbij (fun i : Fin n => g ^ (i : ℕ)) _ fun _ => rfl,
      prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) n]
  obtain ⟨m, hm⟩ := heven
  have hsum : ∑ i ∈ range n, i = m * (n - 1) := by
    have := sum_range_id_mul_two n
    refine Nat.eq_of_mul_eq_mul_right (m := 2) (by norm_num) ?_
    rw [this, hm]
    ring
  rw [hprod, ← pow_mul, hsum, Ne, ← orderOf_dvd_iff_pow_eq_one, hg, hm]
  intro h
  have hm0 : 0 < m := by omega
  rw [mul_assoc, ← two_mul] at h
  rw [mul_comm 2 m] at h
  have h2 : 2 ∣ (m * 2 - 1) * k := Nat.dvd_of_mul_dvd_mul_left hm0 h
  have hn1 : Odd (m * 2 - 1) := ⟨m - 1, by omega⟩
  have hodd : Odd ((m * 2 - 1) * k) := hn1.mul hk
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Lemmas

variable {G : Type*} [Group G] [Finite G]

/-- A group with a nontrivial cyclic Sylow 2-subgroup has no complete mapping. -/
theorem not_hasCompleteMapping_of_sylow_cyclic (P : Sylow 2 G) (hne : (P : Subgroup G) ≠ ⊥)
    (hcyc : IsCyclic P) : ¬ HasCompleteMapping G := by
  rintro ⟨θ, hθ⟩
  have := Fintype.ofFinite G
  classical
  have hPeven : 2 ∣ Nat.card P := by
    rcases P.isPGroup'.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  have hGeven : 2 ∣ Nat.card G := hPeven.trans (Subgroup.card_subgroup_dvd_card _)
  have hmin : (Nat.card G).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr hGeven
  have hcomp := IsCyclic.isComplement' hmin hcyc
  set φ := MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)
  letI : CommGroup P := IsCyclic.commGroup
  have hcard : Nat.card φ.range = Nat.card P := by
    have h1 := hcomp.card_mul
    have h2 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h2
    have hk : 0 < Nat.card φ.ker := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hk (h2.trans h1.symm)
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ hcard
  obtain ⟨c, hc, hprod⟩ := exists_prod_eq_pow_of_surjective (A := P) φ hsurj
  have hcodd : Odd c := by
    have hidx := Subgroup.card_mul_index (P : Subgroup G)
    have hP0 : 0 < Nat.card P := Nat.card_pos
    have : c = (P : Subgroup G).index :=
      Nat.eq_of_mul_eq_mul_left hP0 (by rw [mul_comm, hc, hidx])
    rw [this, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact P.not_dvd_index
  exact prod_univ_pow_ne_one (A := P) (even_iff_two_dvd.mpr hPeven) hcodd
    (hprod ▸ prod_eq_one_of_isCompleteMapping (A := P) φ hθ)

/-- **Hall–Paige (1955), Theorem 5.** A finite group with a complete mapping satisfies the
Hall–Paige condition: its Sylow 2-subgroups are trivial or non-cyclic. -/
theorem isGood_of_hasCompleteMapping (h : HasCompleteMapping G) : IsGood G := by
  intro P
  by_contra hP
  push Not at hP
  exact not_hasCompleteMapping_of_sylow_cyclic P hP.1 hP.2 h

end CFSGOutside.HallPaige
