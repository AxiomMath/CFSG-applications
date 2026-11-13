import CFSGOutside.Corpus.Defs.LieOrder
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Serre (2013), Théorème 5: the order data of a group of Lie type

J.-P. Serre, *Un critère d'indépendance pour une famille de représentations ℓ-adiques*,
Comment. Math. Helv. 88 (2013), 541-554, §6.4. Artin's argument for Théorème 5 uses that the order of a group
of Lie type in characteristic `p ≥ 5` has the form `M · D = q ^ N · C` with `p ∤ D` and `N ≥ 1`. This file shows
that every valid Lie type index of characteristic at least five has such order data (`Good`), from the order
formulas copied in `CFSGOutside.Corpus.Defs.LieOrder`.
-/

namespace CFSGOutside.Serre

open Finset CFSGOutside.Corpus.Open CFSGOutside.Corpus.ComponentClassification.CatLeaf
  CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.I1420

/-- The order data needed for Artin's argument (Serre (2013), §6.4): `M · D = q^N · C` is an admissible
order formula in characteristic `p`, with `p ∤ D` and `N ≥ 1`. -/
def Good (p M : ℕ) : Prop :=
  ∃ t n f, StatedLieAdmissible t n p f ∧
    M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) ∧
    Nat.Coprime p (lieOrderDivisor t n (p ^ f)) ∧
    (p ^ f) ^ lieSylowExponent t n ∣ lieOrderNumerator t n (p ^ f) ∧
    0 < lieSylowExponent t n

/-- Package the data of an admissible order formula as `Good p M`. -/
theorem good_of {p M : ℕ} (t : StatedLieTag) (n f : ℕ) (hadm : StatedLieAdmissible t n p f)
    (hM : M = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f))
    (hD : lieOrderDivisor t n (p ^ f) ∣ lieOrderNumerator t n (p ^ f))
    (hcop : Nat.Coprime p (lieOrderDivisor t n (p ^ f)))
    (hP : (p ^ f) ^ lieSylowExponent t n ∣ lieOrderNumerator t n (p ^ f))
    (hpos : 0 < lieSylowExponent t n) : Good p M :=
  ⟨t, n, f, hadm, by rw [hM, Nat.div_mul_cancel hD], hcop, hP, hpos⟩

/-- `p` is coprime to `p ^ f - 1`. -/
theorem coprime_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    Nat.Coprime p (p ^ f - 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self hpos] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- `p` is coprime to `p ^ f + 1`. -/
theorem coprime_pow_add_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    Nat.Coprime p (p ^ f + 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  have : p ∣ 1 := (Nat.dvd_add_right h1).1 h
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- A prime `p ≥ 5` is coprime to every divisor of `12`. -/
theorem coprime_of_dvd_twelve {p c : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hc : c ∣ 12) :
    Nat.Coprime p c := by
  refine Nat.Coprime.coprime_dvd_right hc ?_
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 ^ 2 * 3 from h) with h4 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4)
    omega
  · have := Nat.le_of_dvd (by norm_num) h3
    omega

/-- `Q - 1` divides `Q ^ 2 - 1`. -/
theorem sub_one_dvd_sq_sub_one (Q : ℕ) : Q - 1 ∣ Q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  refine ⟨Q + 1, ?_⟩
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  zify [h1, hQ]
  ring

/-- `Q + 1` divides `Q ^ 2 - 1`. -/
theorem add_one_dvd_sq_sub_one {Q : ℕ} (hQ : 1 ≤ Q) : Q + 1 ∣ Q ^ 2 - 1 := by
  refine ⟨Q - 1, ?_⟩
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  zify [h1, hQ]
  ring

/-- `m (m - 1) / 2` is positive for `m ≥ 2`. -/
theorem tri_pos {m : ℕ} (hm : 2 ≤ m) : 0 < m * (m - 1) / 2 := by
  have h1 : 1 ≤ m - 1 := by omega
  have h2 : 2 ≤ m * (m - 1) := le_trans (by omega : 2 ≤ m * 1) (Nat.mul_le_mul_left _ h1)
  exact Nat.div_pos h2 two_pos

/-- Every valid Lie type index of characteristic `p ≥ 5` has `Good` order data (Serre (2013), §6.4, the
shape `q ^ N * C / D` of the order of a group of Lie type used in Artin's argument). -/
theorem good_lieOrderFormula (d : TauCeti.LieTypeIndex) (hd : d.Valid)
    (h5 : 5 ≤ d.characteristic) : Good d.characteristic (lieOrderFormula d) := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | suzuki m => simp at h5
  | reeG2 m => simp at h5
  | reeF4 m => simp at h5
  | tits => simp at h5
  | A n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_A] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    have hQ : 5 ≤ q.p ^ q.exponent := le_trans h5 (Nat.le_self_pow hf.ne' _)
    refine good_of .PSL (n + 1) q.exponent ⟨hp, hf, by omega, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def, Nat.add_sub_cancel, mul_comm (n + 1) n]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one _).trans ?_)
      exact (Finset.dvd_prod_of_mem (fun i => (q.p ^ q.exponent) ^ i - 1)
        (by simp only [Finset.mem_Icc]; omega)).trans (dvd_mul_left _ _)
    · exact (coprime_pow_sub_one hp hf).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    · simp only [lieOrderNumerator, lieSylowExponent]; exact dvd_mul_right _ _
    · exact tri_pos (by omega)
  | twistedA n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    have hQ : 5 ≤ q.p ^ q.exponent := le_trans h5 (Nat.le_self_pow hf.ne' _)
    refine good_of .PSU (n + 1) q.exponent ⟨hp, hf, by omega, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def, Nat.add_sub_cancel, mul_comm (n + 1) n]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      refine (Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one (by omega)).trans ?_)
      have h2 := Finset.dvd_prod_of_mem
        (fun i => if Even i then (q.p ^ q.exponent) ^ i - 1 else (q.p ^ q.exponent) ^ i + 1)
        (show 2 ∈ Icc 2 (n + 1) by simp only [Finset.mem_Icc]; omega)
      simp only [show Even 2 from even_two, if_true] at h2
      exact h2.trans (dvd_mul_left _ _)
    · exact (coprime_pow_add_one hp hf).coprime_dvd_right (Nat.gcd_dvd_right _ _)
    · simp only [lieOrderNumerator, lieSylowExponent]; exact dvd_mul_right _ _
    · exact tri_pos (by omega)
  | B n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_B] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    have hQ : 5 ≤ q.p ^ q.exponent := le_trans h5 (Nat.le_self_pow hf.ne' _)
    refine good_of .PSp n q.exponent ⟨hp, hf, by omega, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [lieOrderFormula, orderBC, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def, sq]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one _).trans ?_)
      have h2 := Finset.dvd_prod_of_mem (fun i => (q.p ^ q.exponent) ^ (2 * i) - 1)
        (show 1 ∈ Icc 1 n by simp only [Finset.mem_Icc]; omega)
      simp only [mul_one] at h2
      exact h2.trans (dvd_mul_left _ _)
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]; exact dvd_mul_right _ _
    · simp only [lieSylowExponent]; exact pow_pos (by omega) 2
  | C n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_C] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    have hQ : 5 ≤ q.p ^ q.exponent := le_trans h5 (Nat.le_self_pow hf.ne' _)
    refine good_of .PSp n q.exponent ⟨hp, hf, by omega, ?_⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [lieOrderFormula, orderBC, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def, sq]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      refine (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one _).trans ?_)
      have h2 := Finset.dvd_prod_of_mem (fun i => (q.p ^ q.exponent) ^ (2 * i) - 1)
        (show 1 ∈ Icc 1 n by simp only [Finset.mem_Icc]; omega)
      simp only [mul_one] at h2
      exact h2.trans (dvd_mul_left _ _)
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]; exact dvd_mul_right _ _
    · simp only [lieSylowExponent]; exact pow_pos (by omega) 2
  | D n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_D] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .POmegaPlus n q.exponent ⟨hp, hf, hs⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [lieOrderFormula, orderD, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      exact (Nat.gcd_dvd_right _ _).trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]
      exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
    · simp only [lieSylowExponent]; exact Nat.mul_pos (by omega) (by omega)
  | twistedD n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedD] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .POmegaMinus n q.exponent ⟨hp, hf, hs⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [lieOrderFormula, orderTwistedD, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      exact (Nat.gcd_dvd_right _ _).trans ((dvd_mul_left _ _).trans (dvd_mul_right _ _))
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]
      exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
    · simp only [lieSylowExponent]; exact Nat.mul_pos (by omega) (by omega)
  | E6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E6] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .E6 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [lieOrderFormula, orderE6, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one _).trans (dvd_mul_left _ _))
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | E7 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E7] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .E7 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [lieOrderFormula, orderE7, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one _).trans (dvd_mul_left _ _))
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | twistedE6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    have hQ : 5 ≤ q.p ^ q.exponent := le_trans h5 (Nat.le_self_pow hf.ne' _)
    refine good_of .twistedE6 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp only [lieOrderFormula, orderTwistedE6, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp only [lieOrderNumerator, lieOrderDivisor]
      exact (Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one (by omega)).trans
        (dvd_mul_left _ _))
    · exact coprime_of_dvd_twelve hp h5 ((Nat.gcd_dvd_left _ _).trans (by norm_num))
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | E8 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_E8] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .E8 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp [lieOrderFormula, orderE8, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp [lieOrderDivisor]
    · simp [lieOrderDivisor]
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | F4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_F4] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .F4 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp [lieOrderFormula, orderF4, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp [lieOrderDivisor]
    · simp [lieOrderDivisor]
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | G2 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_G2] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .G2 0 q.exponent ⟨hp, hf, rfl, by simpa [TauCeti.PrimePower.card_def] using hs⟩
      ?_ ?_ ?_ ?_ ?_
    · simp [lieOrderFormula, orderG2, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp [lieOrderDivisor]
    · simp [lieOrderDivisor]
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]
  | trialityD4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at h5 ⊢
    have hp := q.prime_p
    have hf := q.exponent_pos
    refine good_of .trialityD4 0 q.exponent ⟨hp, hf, rfl⟩ ?_ ?_ ?_ ?_ ?_
    · simp [lieOrderFormula, orderTrialityD4, lieOrderNumerator, lieOrderDivisor,
        TauCeti.PrimePower.card_def]
    · simp [lieOrderDivisor]
    · simp [lieOrderDivisor]
    · simp only [lieOrderNumerator, lieSylowExponent]
      simp only [mul_assoc]
      exact dvd_mul_right _ _
    · simp [lieSylowExponent]

/-- Order data `Good p M` gives `p ^ k ∣ M` for some `k ≥ 1`. -/
theorem pow_dvd_of_good {p M : ℕ} (hg : Good p M) : ∃ k, 1 ≤ k ∧ p ^ k ∣ M := by
  obtain ⟨t, n, f, hadm, hmul, hcop, hP, hpos⟩ := hg
  refine ⟨f * lieSylowExponent t n, Nat.mul_pos hadm.2.1 hpos, ?_⟩
  rw [pow_mul]
  rw [← hmul] at hP
  exact (Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ hcop)).dvd_of_dvd_mul_right hP

/-- If `p ^ k ∣ M` then `p ^ k` is at most the `p`-part of `M`. -/
theorem pow_le_ordProj {p k M : ℕ} (hp : p.Prime) (hM : M ≠ 0) (h : p ^ k ∣ M) :
    p ^ k ≤ ordProj[p] M ∧ k ≤ M.factorization p := by
  have hk := (hp.pow_dvd_iff_le_factorization hM).1 h
  exact ⟨Nat.pow_le_pow_right hp.pos hk, hk⟩

/-- `Good 5 60`: the order of `PSL₂(5)` has the form `M·D = q^N·C` with `p ∤ D`, `N ≥ 1`. -/
theorem good_five_sixty : Good 5 60 := by
  refine good_of .PSL 2 1 ⟨Nat.prime_five, le_refl _, le_refl _, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ <;>
    simp [lieOrderNumerator, lieOrderDivisor, lieSylowExponent] <;> decide

end CFSGOutside.Serre
