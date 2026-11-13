import CFSGOutside.Gagola.Main
import CFSGOutside.Gagola.PSL2DihedralStmt
import CFSGOutside.Corpus.GorensteinWalter
import CFSGOutside.Corpus.BrauerSuzukiQuaternion
import CFSGOutside.Corpus.Order8Nonabelian

/-!
# Gagola, Theorem 4.5: no nonabelian simple quotient with Sylow 2-subgroup of order 8, nonabelian

`sylow8_false`: if `H/K` is nonabelian simple with a nonabelian Sylow 2-subgroup of order 8, we get a
contradiction. The Sylow 2-subgroup is `D₄` or `Q₈`; `Q₈` is excluded by Brauer-Suzuki; for `D₄`,
Gorenstein-Walter gives `A₇` or `PSL(2, q)`; in `A₇` the primes `5, 7` have cyclic Sylow subgroups, in
`PSL(2, q)` use `Psl2OddSylow8`.
-/

namespace CFSGOutside.Gagola

open Classical CFSGOutside.Corpus
open scoped MatrixGroups

noncomputable section

theorem two_primes_false {H : Type} [Group H] [Fintype H] {Z : Subgroup H} {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    (h : TwoCyclicPrimes (H ⧸ K)) : False := by
  obtain ⟨hZ, hχ, θ, e, hθ, hres, he⟩ := hfr
  haveI := hZ
  obtain ⟨p, r, hp, hr, hpr, h1, h2⟩ := h
  obtain ⟨P1⟩ := (inferInstance : Nonempty (Sylow p (H ⧸ K)))
  obtain ⟨P2⟩ := (inferInstance : Nonempty (Sylow r (H ⧸ K)))
  obtain ⟨c1, n1⟩ := h1 P1
  obtain ⟨c2, n2⟩ := h2 P2
  exact thm_2_5_a hχ hθ hres he K hZK hpr P1 c1 n1 P2 c2 n2

theorem cyclic_of_factorization_one {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (h : (Nat.card Y).factorization p = 1) :
    ∀ P : Sylow p Y, IsCyclic (P : Subgroup Y) ∧ Nat.card P ≠ 1 := by
  intro P
  have hc : Nat.card P = p := by rw [Sylow.card_eq_multiplicity, h, pow_one]
  exact ⟨isCyclic_of_prime_card hc, by rw [hc]; exact hp.out.one_lt.ne'⟩

theorem factorization_eq_one_of {n m p : ℕ} [hp : Fact p.Prime] (hn : n = p * m) (hm : ¬ p ∣ m)
    (hm0 : m ≠ 0) : n.factorization p = 1 := by
  rw [hn, Nat.factorization_mul hp.out.ne_zero hm0, Finsupp.add_apply, hp.out.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]

theorem twoCyclicPrimes_A7 : TwoCyclicPrimes (alternatingGroup (Fin 7)) := by
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨5, 7, inferInstance, inferInstance, by norm_num, ?_, ?_⟩
  · exact cyclic_of_factorization_one (factorization_eq_one_of (m := 504) (by rw [hcard]) (by norm_num)
      (by norm_num))
  · exact cyclic_of_factorization_one (factorization_eq_one_of (m := 360) (by rw [hcard]) (by norm_num)
      (by norm_num))

theorem sylow8_false [GorensteinWalter] [BrauerSuzukiQuaternion] [Order8Nonabelian]
    {H : Type} [Group H] [Fintype H] {Z : Subgroup H} [Z.Normal] {χ : H → ℂ}
    (hfr : FullyRamified Z χ) (K : Subgroup H) [K.Normal] (hZK : Z ≤ K) [IsSimpleGroup (H ⧸ K)]
    (hnonab : ∃ a b : H ⧸ K, a * b ≠ b * a) (S : Sylow 2 (H ⧸ K)) (hS : Nat.card S = 8)
    (hSnab : ¬ IsMulCommutative (S : Subgroup (H ⧸ K))) (hpsl : Psl2OddSylow8) : False := by
  have hnab : ∃ a b : (S : Subgroup (H ⧸ K)), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact hSnab ⟨⟨fun a b => hc a b⟩⟩
  rcases Order8Nonabelian.order8_nonabelian (G := (S : Subgroup (H ⧸ K))) hS hnab with
    ⟨e⟩ | ⟨e⟩
  swap
  · exact BrauerSuzukiQuaternion.false_of_sylow_quaternion hnonab S e.some
  rcases GorensteinWalter.gorenstein_walter (H ⧸ K) hnonab S ⟨4, e⟩ with φ | ⟨p, k, hp, hpodd, h5, φ⟩
  · exact two_primes_false hfr K hZK (twoCyclicPrimes_A7.of_mulEquiv φ.some)
  · letI := Fintype.ofFinite (GaloisField p k)
    have hk : k ≠ 0 := by
      rintro rfl
      simp at h5
    have hcard : Fintype.card (GaloisField p k) = p ^ k := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
    have hfac : (Nat.card PSL(2, GaloisField p k)).factorization 2 = 3 := by
      rw [← Nat.card_congr φ.some.toEquiv]
      have h1 : (2 : ℕ) ^ ((Nat.card (H ⧸ K)).factorization 2) = 8 := by
        rw [← Sylow.card_eq_multiplicity]; exact hS
      have h2 : (2 : ℕ) ^ ((Nat.card (H ⧸ K)).factorization 2) = 2 ^ 3 := by rw [h1]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h2
    rcases hpsl (GaloisField p k) (by rw [hcard]; exact hpodd.pow) (by rw [hcard]; exact h5) hfac with
      h | ⟨-, h360, h5c⟩
    · exact two_primes_false hfr K hZK (h.of_mulEquiv φ.some)
    · obtain ⟨hZ, hχ, θ, e', hθ, hres, he⟩ := hfr
      have hX : Nat.card (H ⧸ K) = 360 := by rw [Nat.card_congr φ.some.toEquiv, h360]
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 (H ⧸ K)))
      let P' := P.mapSurjective (f := φ.some.toMonoidHom) φ.some.surjective
      obtain ⟨hc', hn'⟩ := h5c P'
      have hP' : (P' : Subgroup PSL(2, GaloisField p k)) = (P : Subgroup (H ⧸ K)).map φ.some.toMonoidHom :=
        Sylow.coe_mapSurjective _ _
      have hPcard : Nat.card P = 5 := by
        have h' : Nat.card (P' : Subgroup PSL(2, GaloisField p k)) = 5 := hn'
        rw [hP', Subgroup.card_map_of_injective φ.some.injective] at h'
        exact h'
      have hcyc : IsCyclic (P : Subgroup (H ⧸ K)) := isCyclic_of_prime_card (α := (P : Subgroup (H ⧸ K))) (p := 5) hPcard
      haveI := hZ
      obtain ⟨M, hM⟩ := thm_2_5 hχ hθ hres he K hZK P hcyc
      rw [hPcard] at hM
      have hMne : M ≠ ⊤ := by rintro rfl; simp at hM
      have := card_le_factorial_index hMne
      rw [hM, hX] at this
      simp [Nat.factorial] at this

end

end CFSGOutside.Gagola
