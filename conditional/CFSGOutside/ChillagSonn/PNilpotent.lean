import CFSGOutside.Corpus.FrobeniusNormalPComplement
import CFSGOutside.Corpus.FrattiniQuotientFacts
import CFSGOutside.ChillagSonn.Metacyclic

/-!
# A `p`-nilpotency criterion for metacyclic Sylow `p`-subgroups

The `p`-nilpotency step behind the Sylow tower in Chillag–Sonn (Lemma 1.4; [Gorenstein, p. 259]): if the Sylow
`p`-subgroups of `G` are metacyclic and no prime `r ≠ p` dividing `|G|` divides `p - 1` or `p + 1`, then `G` has a
normal `p`-complement.

By Frobenius it suffices that `N_G(Q)/C_G(Q)`, which embeds in `Aut(Q)`, is a `p`-group for each `p`-subgroup `Q`.
An automorphism `σ` of `Q` of prime order `r ≠ p` induces `τ` on `V = Q/Φ(Q)`, which is metacyclic of exponent `p`,
so `|V| ∣ p²`; counting fixed points of `⟨τ⟩` modulo `r` shows `τ = 1`, so `σ` lies in the kernel of
`Aut(Q) → Aut(Q/Φ(Q))`, a `p`-group (Burnside), whence `σ = 1`.
-/

namespace CFSGOutside.ChillagSonn

open CFSGOutside.Corpus CFSGOutside.Corpus.GroupTheory OrderReductions.FrattiniAutomorphisms

/-- An automorphism `τ` with `τ ^ r = 1` of a group of order dividing `p²`, for a prime `r` not dividing
`p (p - 1) (p + 1)`, is trivial (count fixed points of `⟨τ⟩` modulo `r`). -/
theorem eq_one_of_pow_eq_one_of_card_dvd_sq {V : Type*} [Group V] [Finite V] {p r : ℕ} [hp : Fact p.Prime]
    [hr : Fact r.Prime] (hV : Nat.card V ∣ p ^ 2) (hrp : r ≠ p) (h1 : ¬ r ∣ p - 1) (h2 : ¬ r ∣ p + 1)
    {τ : MulAut V} (hτ : τ ^ r = 1) : τ = 1 := by
  rcases (Nat.dvd_prime hr.out).mp (orderOf_dvd_of_pow_eq_one hτ) with h | h
  · exact orderOf_eq_one_iff.mp h
  have hH : IsPGroup r (Subgroup.zpowers τ) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  set F := FixedPoints.subgroup (Subgroup.zpowers τ) V
  have hmod := hH.card_modEq_card_fixedPoints V
  change Nat.card V ≡ Nat.card F [MOD r] at hmod
  by_cases hF : F = ⊤
  · ext v
    exact (FixedPoints.mem_subgroup _ _ v).mp (hF ▸ Subgroup.mem_top v) ⟨τ, Subgroup.mem_zpowers τ⟩
  obtain ⟨j, hj, hVj⟩ := (Nat.dvd_prime_pow hp.out).mp hV
  obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow hp.out).mp (hVj ▸ F.card_subgroup_dvd_card)
  have hij : i < j := by
    refine lt_of_le_of_ne hi fun hij ↦ hF ?_
    rw [← Subgroup.card_eq_iff_eq_top, hFi, hVj, hij]
  rw [hVj, hFi] at hmod
  have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.out.pos hi)).mp hmod.symm
  have hrp' : ¬ r ∣ p := fun h ↦ hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp.out).mp h)
  exfalso
  interval_cases j <;> interval_cases i
  · exact h1 (by simpa using hd)
  · refine (hr.out.dvd_mul.mp ?_).elim h2 h1
    rwa [pow_zero, show p ^ 2 - 1 = (p + 1) * (p - 1) by simpa using Nat.sq_sub_sq p 1] at hd
  · refine (hr.out.dvd_mul.mp ?_).elim hrp' h1
    rwa [pow_one, sq, ← Nat.mul_sub_one] at hd

/-- In a metacyclic `p`-group, an automorphism `σ` with `σ ^ r = 1`, for a prime `r ≠ p` dividing neither `p - 1`
nor `p + 1`, is trivial. -/
theorem eq_one_of_pow_eq_one_of_isMetacyclic [FrattiniElementaryQuotient.{0}] [FrattiniAutomorphismKernel.{0}]
    {Q : Type} [Group Q] [Finite Q] {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime] (hQ : IsPGroup p Q)
    (hM : IsMetacyclic Q) (hrp : r ≠ p) (h1 : ¬ r ∣ p - 1) (h2 : ¬ r ∣ p + 1) {σ : MulAut Q} (hσ : σ ^ r = 1) :
    σ = 1 := by
  obtain ⟨-, -, hexp, -⟩ := FrattiniElementaryQuotient.frattini_elementary_quotient hQ
  have hV : Nat.card (Q ⧸ frattini Q) ∣ p ^ 2 :=
    (hM.of_surjective _ (QuotientGroup.mk'_surjective _)).card_dvd_sq hexp
  have hτ : quotientAutomorphism (frattini Q) σ = 1 :=
    eq_one_of_pow_eq_one_of_card_dvd_sq hV hrp h1 h2 (by rw [← map_pow, hσ, map_one])
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (FrattiniAutomorphismKernel.frattini_automorphism_kernel hQ).2 ⟨σ, MonoidHom.mem_ker.mpr hτ⟩
  replace hk := (Subgroup.orderOf_coe _).trans hk
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (((Nat.coprime_primes hr.out hp.out).mpr hrp).pow_right k)
    (orderOf_dvd_of_pow_eq_one hσ) (hk ▸ dvd_rfl))

/-- If the Sylow `p`-subgroups of `G` are metacyclic and no prime `r ≠ p` dividing `|G|` divides `p - 1` or `p + 1`,
then `G` has a normal `p`-complement. -/
theorem exists_normalPComplement_of_metacyclic [FrobeniusNormalPComplement.{0}] [FrattiniElementaryQuotient.{0}]
    [FrattiniAutomorphismKernel.{0}] {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hP : ∀ P : Sylow p G, IsMetacyclic P)
    (hr : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → r ≠ p → ¬ r ∣ p - 1 ∧ ¬ r ∣ p + 1) :
    ∃ N : Subgroup G, IsNormalPComplement p N := by
  refine (FrobeniusNormalPComplement.frobenius_normal_p_complement p).1.mpr fun Q hQ ↦ ?_
  have hM : IsMetacyclic Q := by
    obtain ⟨S, hS⟩ := hQ.exists_le_sylow
    exact (hP S).of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
  let φ := Q.normalizerMonoidHom
  refine IsPGroup.of_equiv ?_ ((QuotientGroup.quotientMulEquivOfEq Q.normalizerMonoidHom_ker).symm.trans
    (QuotientGroup.quotientKerEquivRange φ)).symm
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hrp hrd ↦ ?_)
  by_contra hne
  have := Fact.mk hrp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) r hrd
  rw [← Subgroup.orderOf_coe] at hx
  obtain ⟨h1, h2⟩ := hr r hrp (hrd.trans ((Subgroup.card_range_dvd φ).trans (Subgroup.card_subgroup_dvd_card _))) hne
  have h := eq_one_of_pow_eq_one_of_isMetacyclic hQ hM hne h1 h2 (σ := (x : MulAut Q))
    (hx ▸ pow_orderOf_eq_one _)
  rw [h, orderOf_one] at hx
  exact hrp.one_lt.ne hx

end CFSGOutside.ChillagSonn
