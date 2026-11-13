import CFSGOutside.Gagola.PSL2DihedralStmt

/-!
# `PSL(2, q)`, `q` odd, with Sylow 2-subgroups of order 8
-/

namespace CFSGOutside.Gagola

open Classical Matrix
open scoped MatrixGroups

noncomputable section

section Aux

variable (F : Type) [Field F] [Fintype F]

theorem center_scalar (z : Subgroup.center SL(2, F)) :
    ∃ c : F, c ^ 2 = 1 ∧ Matrix.scalar (Fin 2) c = ((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc2, hcz⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp z.2
  simp only [Fintype.card_fin] at hc2
  exact ⟨c, hc2, hcz⟩

theorem card_center_le : Nat.card (Subgroup.center SL(2, F)) ≤ 2 := by
  let g : Subgroup.center SL(2, F) → Bool := fun z => decide (((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1)
  have key : ∀ z : Subgroup.center SL(2, F), ∃ c : F, (c = 1 ∨ c = -1) ∧
      Matrix.scalar (Fin 2) c = ((z : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro z
    obtain ⟨c, hc, hcz⟩ := center_scalar F z
    refine ⟨c, ?_, hcz⟩
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.mp this
  have hinj : Function.Injective g := by
    intro z1 z2 h
    obtain ⟨c1, h1, e1⟩ := key z1
    obtain ⟨c2, h2, e2⟩ := key z2
    have g1 : ((z1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = c1 := by rw [← e1]; simp
    have g2 : ((z2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = c2 := by rw [← e2]; simp
    have hc : c1 = c2 := by
      simp only [g, g1, g2, decide_eq_decide] at h
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · rfl
      · exact (h.mp rfl).symm
      · exact h.mpr rfl
      · rfl
    apply Subtype.ext; apply Subtype.ext
    rw [← e1, ← e2, hc]
  have := Nat.card_le_card_of_injective g hinj
  simpa using this

theorem vp_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem odd_prime_or_pow (n : ℕ) (hn : n ≠ 0) :
    n = 2 ^ n.factorization 2 ∨ ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ n := by
  by_cases h : n / 2 ^ n.factorization 2 = 1
  · left
    have := Nat.ordProj_mul_ordCompl_eq_self n 2
    rw [h] at this
    simpa using this.symm
  · right
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h
    refine ⟨r, hr, ?_, hrd.trans (Nat.ordCompl_dvd n 2)⟩
    rintro rfl
    exact Nat.not_dvd_ordCompl Nat.prime_two hn hrd

theorem psl2_prime_sylow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (h : (Nat.card SL(2, F)).factorization p = 1) :
    ∀ P : Sylow p PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P = p := by
  intro P
  have hcard : Nat.card P = p := by
    rw [Sylow.card_eq_multiplicity, factorization_card_PSL2 F hp2, h, pow_one]
  exact ⟨isCyclic_of_prime_card hcard, hcard⟩

end Aux

theorem psl2OddSylow8 : Psl2OddSylow8 := by
  intro F _ _ hodd h5 h2
  have hZpos : 0 < Nat.card (Subgroup.center SL(2, F)) := Nat.card_pos
  have hZle := card_center_le F
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  have hPSL : Nat.card PSL(2, F) = Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) := rfl
  rw [← hPSL] at hprod
  have hq : 1 < Fintype.card F := by omega
  set q := Fintype.card F with hqdef
  have hSL := card_SL2 F
  rw [← hqdef] at hSL
  have hPpos : 0 < Nat.card PSL(2, F) := Nat.card_pos
  have hq0 : q ≠ 0 := by omega
  have hqm : q - 1 ≠ 0 := by omega
  have hqp : q + 1 ≠ 0 := by omega
  have hq2 : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => by obtain ⟨k, hk⟩ := hodd; omega)
  -- v2 of |SL|
  have hv : (q - 1).factorization 2 + (q + 1).factorization 2 ≤ 4 := by
    have e : (Nat.card SL(2, F)).factorization 2 =
        (Nat.card (Subgroup.center SL(2, F))).factorization 2 + 3 := by
      rw [hprod, Nat.factorization_mul hPpos.ne' hZpos.ne', Finsupp.add_apply, h2, add_comm]
    have hZ : (Nat.card (Subgroup.center SL(2, F))).factorization 2 ≤ 1 := by
      generalize Nat.card (Subgroup.center SL(2, F)) = z at hZpos hZle
      interval_cases z
      · simp
      · simp [Nat.Prime.factorization_self Nat.prime_two]
    have e2 : (Nat.card SL(2, F)).factorization 2 =
        (q - 1).factorization 2 + (q + 1).factorization 2 := by
      rw [hSL, Nat.factorization_mul (Nat.mul_ne_zero hq0 hqm) hqp,
        Nat.factorization_mul hq0 hqm]
      simp [hq2]
    omega
  have ha : 1 ≤ (q - 1).factorization 2 := by
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hqm).mp
      (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
    exact this
  have hb : 1 ≤ (q + 1).factorization 2 := by
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hqp).mp
      (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
    exact this
  have final : q = 5 ∨ q = 7 ∨ q = 9 → TwoCyclicPrimes PSL(2, F) ∨
      (Fintype.card F = 9 ∧ Nat.card PSL(2, F) = 360 ∧
        ∀ P : Sylow 5 PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P = 5) := by
    intro hcase
    rcases hcase with h | h | h
    · exact Or.inl (psl2_two_primes F (Or.inr ⟨hodd, h5, by omega⟩))
    · have hF : Fintype.card F = 7 := h
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine Or.inl ⟨3, 7, inferInstance, inferInstance, by norm_num, ?_, ?_⟩
      · exact psl2_cyclic_sylow F (by norm_num)
          (Or.inl ⟨by rw [hF]; norm_num, by rw [hF]; norm_num⟩) (by rw [hF]; norm_num)
      · have h7 : (Nat.card SL(2, F)).factorization 7 = 1 := by
          rw [hSL, h]
          have : (7 * (7 - 1) * (7 + 1) : ℕ) = 7 ^ 1 * 48 := by norm_num
          rw [this]
          exact vp_mul (by norm_num) 1 48 (by norm_num) (by norm_num)
        intro P
        obtain ⟨c, hc⟩ := psl2_prime_sylow F (p := 7) (by norm_num) h7 P
        exact ⟨c, by rw [hc]; norm_num⟩
    · have hF : Fintype.card F = 9 := h
      refine Or.inr ⟨h, ?_, ?_⟩
      · have h720 : Nat.card SL(2, F) = 720 := by rw [hSL, h]
        rw [h720] at hprod
        generalize Nat.card (Subgroup.center SL(2, F)) = z at hZpos hZle hprod
        generalize hw : Nat.card PSL(2, F) = w at hprod h2
        interval_cases z
        · have hw' : w = 720 := by omega
          subst hw'
          have : (720 : ℕ) = 2 ^ 4 * 45 := by norm_num
          rw [this, vp_mul Nat.prime_two 4 45 (by norm_num) (by norm_num)] at h2
          omega
        · omega
      · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        have h5' : (Nat.card SL(2, F)).factorization 5 = 1 := by
          rw [hSL, h]
          have : (9 * (9 - 1) * (9 + 1) : ℕ) = 5 ^ 1 * 144 := by norm_num
          rw [this]
          exact vp_mul (by norm_num) 1 144 (by norm_num) (by norm_num)
        exact psl2_prime_sylow F (p := 5) (by norm_num) h5'
  rcases odd_prime_or_pow (q - 1) hqm with h1 | ⟨r, hr, hr2, hr1⟩
  · have : q - 1 ≤ 2 ^ 3 := by
      rw [h1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq' : q = 5 ∨ q = 7 ∨ q = 9 := by
      obtain ⟨k, hk⟩ := hodd; omega
    exact final hq'
  · rcases odd_prime_or_pow (q + 1) hqp with h1 | ⟨r', hr', hr'2, hr'1⟩
    · have : q + 1 ≤ 2 ^ 3 := by
        rw [h1]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hq' : q = 5 ∨ q = 7 := by
        obtain ⟨k, hk⟩ := hodd; omega
      exact final (by omega)
    · exact Or.inl (psl2_two_primes_of F hr hr2 hr' hr'2 hr1 hr'1)

end

end CFSGOutside.Gagola
