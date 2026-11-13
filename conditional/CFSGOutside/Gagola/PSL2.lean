import Mathlib

/-!
# Cyclic Sylow subgroups of `PSL(2, q)`

`SL(2, q)` contains cyclic subgroups of orders `q - 1` (the split torus, diagonal matrices) and `q + 1`
(the non-split torus, the norm-one units of the quadratic extension acting on it by multiplication).
Hence for an odd prime `r ∤ q` dividing `q² - 1` the Sylow `r`-subgroups of `SL(2, q)`, and of `PSL(2, q)`,
are cyclic. For the groups `PSL(2, q)` in Walter's list (`q = 2^f ≥ 4`, or `q ≡ ±3 (mod 8)` with `q ≥ 5`)
we find two distinct primes with nontrivial cyclic Sylow subgroups.
-/

namespace CFSGOutside.Gagola

open Classical Matrix
open scoped MatrixGroups

noncomputable section

section Generic

variable {G : Type*} [Group G] [Finite G]

/-- If a cyclic subgroup has the full `r`-part of `|G|`, the Sylow `r`-subgroups of `G` are cyclic. -/
theorem isCyclic_sylow_of_cyclic_subgroup {r : ℕ} [Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (h : (Nat.card G).factorization r = (Nat.card C).factorization r) (P : Sylow r G) :
    IsCyclic (P : Subgroup G) := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r C))
  set A : Subgroup G := (Q : Subgroup C).map C.subtype
  have hcard : Nat.card A = r ^ (Nat.card G).factorization r := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective C), Sylow.card_eq_multiplicity, h]
  let P' : Sylow r G := Sylow.ofCard A hcard
  have hA : IsCyclic A :=
    isCyclic_of_surjective (C.subtype.subgroupMap (Q : Subgroup C)) (C.subtype.subgroupMap_surjective _)
  have hP' : IsCyclic (P' : Subgroup G) := hA
  exact isCyclic_of_injective (Sylow.equiv P P').toMonoidHom (Sylow.equiv P P').injective

/-- Sylow subgroups of a quotient by a subgroup whose order is prime to `r`. -/
theorem isCyclic_sylow_quotient {r : ℕ} [Fact r.Prime] (N : Subgroup G) [N.Normal]
    (hcyc : ∀ P : Sylow r G, IsCyclic (P : Subgroup G)) (P : Sylow r (G ⧸ N)) :
    IsCyclic (P : Subgroup (G ⧸ N)) := by
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow r G))
  let P₁ := P₀.mapSurjective (QuotientGroup.mk'_surjective N)
  have h1 : IsCyclic (P₁ : Subgroup (G ⧸ N)) := by
    have := hcyc P₀
    show IsCyclic ((P₀ : Subgroup G).map (QuotientGroup.mk' N))
    exact isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap (P₀ : Subgroup G))
      ((QuotientGroup.mk' N).subgroupMap_surjective _)
  exact isCyclic_of_injective (Sylow.equiv P P₁).toMonoidHom (Sylow.equiv P P₁).injective

end Generic

section Tori

variable (F : Type) [Field F] [Fintype F]

/-- The split torus `a ↦ diag(a, a⁻¹)`. -/
def splitHom : Fˣ →* SL(2, F) where
  toFun a := ⟨!![(a : F), 0; 0, (a⁻¹ : Fˣ)], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change _ = !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem splitHom_injective : Function.Injective (splitHom F) := by
  intro a b h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [splitHom] at this
  exact Units.ext this

theorem exists_cyclic_sub_one :
    ∃ C : Subgroup SL(2, F), IsCyclic C ∧ Nat.card C = Fintype.card F - 1 := by
  refine ⟨(splitHom F).range, ?_, ?_⟩
  · exact isCyclic_of_surjective (splitHom F).rangeRestrict (splitHom F).rangeRestrict_surjective
  · rw [← Nat.card_congr (MonoidHom.ofInjective (splitHom_injective F)).toEquiv, Nat.card_units,
      Nat.card_eq_fintype_card]

theorem exists_cyclic_add_one :
    ∃ C : Subgroup SL(2, F), IsCyclic C ∧ Nat.card C = Fintype.card F + 1 := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  set E := FiniteField.Extension F (ringChar F) 2
  have hfin : Module.finrank F E = 2 := FiniteField.finrank_extension F (ringChar F) 2
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfin
  let lm := Algebra.leftMulMatrix b
  let Nm : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)
  let ψ : Nm.ker →* SL(2, F) :=
    { toFun := fun u => ⟨lm ((u : Eˣ) : E), by
        rw [← Algebra.norm_eq_matrix_det b]
        have := u.2
        rw [MonoidHom.mem_ker] at this
        have h2 := congrArg (fun v : Fˣ => (v : F)) this
        simpa [Nm] using h2⟩
      map_one' := by ext; simp
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul, Units.val_mul, map_mul]; rfl) }
  have hψinj : Function.Injective ψ := by
    intro u v h
    have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
    have h2 : ((u : Eˣ) : E) = ((v : Eˣ) : E) := Algebra.leftMulMatrix_injective b h1
    exact Subtype.ext (Units.ext h2)
  have hNmsurj : Function.Surjective Nm := FiniteField.unitsMap_norm_surjective F E
  have hcardE : Nat.card E = Fintype.card F ^ 2 := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
  have hker : Nat.card Nm.ker = Fintype.card F + 1 := by
    have h := Subgroup.card_ker_mul_card_range Nm
    rw [MonoidHom.range_eq_top.mpr hNmsurj, Subgroup.card_top, Nat.card_units, Nat.card_units,
      hcardE, Nat.card_eq_fintype_card (α := F)] at h
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 - 1 = (Fintype.card F + 1) * (Fintype.card F - 1) := by
      have h1 : 1 ≤ Fintype.card F := le_of_lt hq
      have h2 : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h2]
      ring
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  refine ⟨ψ.range, ?_, ?_⟩
  · exact isCyclic_of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, hker]

end Tori

section Cards

variable (F : Type) [Field F] [Fintype F]

theorem card_SL2 : Nat.card SL(2, F) = Fintype.card F * (Fintype.card F - 1) * (Fintype.card F + 1) := by
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have h1 : (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) =
      (Fintype.card F * (Fintype.card F - 1) * (Fintype.card F + 1)) * (Fintype.card F - 1) := by
    have hq1 : 1 ≤ Fintype.card F := le_of_lt hq
    have hq2 : Fintype.card F ≤ Fintype.card F ^ 2 := by nlinarith
    have hq3 : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1, hq3, hq2]
    ring
  rw [h1, Nat.mul_div_cancel _ (by omega)]

/-- The centre of `SL(2, F)` has no elements of odd prime order. -/
theorem not_dvd_card_center {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (Subgroup.center SL(2, F)) := by
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center SL(2, F)) r hdvd
  have hzc := (z : SL(2, F))
  obtain ⟨c, hc2, hcz⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp z.2
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [Fintype.card_fin] at hc2
    simp only [SubmonoidClass.coe_pow, Matrix.SpecialLinearGroup.coe_pow, OneMemClass.coe_one,
      Matrix.SpecialLinearGroup.coe_one, ← hcz]
    rw [← map_pow, hc2, map_one]
  have := orderOf_dvd_of_pow_eq_one hz2
  rw [hz] at this
  have := Nat.le_of_dvd (by norm_num) this
  have := hr.out.two_le
  omega

/-- For an odd prime, the `r`-parts of `|SL(2, F)|` and `|PSL(2, F)|` agree. -/
theorem factorization_card_PSL2 {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) :
    (Nat.card PSL(2, F)).factorization r = (Nat.card SL(2, F)).factorization r := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  have hPSL : Nat.card PSL(2, F) = Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) := rfl
  rw [hPSL, h, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_card_center F hr2), add_zero]

end Cards

section Sylow

variable (F : Type) [Field F] [Fintype F]

/-- An odd prime `r` dividing exactly one of `q - 1`, `q + 1` and not `q` has nontrivial cyclic Sylow
subgroups in `PSL(2, q)`. -/
theorem psl2_cyclic_sylow {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hcase : (r ∣ Fintype.card F - 1 ∧ ¬ r ∣ Fintype.card F + 1) ∨
      (r ∣ Fintype.card F + 1 ∧ ¬ r ∣ Fintype.card F - 1))
    (hrq : ¬ r ∣ Fintype.card F) :
    ∀ P : Sylow r PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hq0 : Fintype.card F ≠ 0 := by omega
  have hqm : Fintype.card F - 1 ≠ 0 := by omega
  have hqp : Fintype.card F + 1 ≠ 0 := by omega
  have hSL : (Nat.card SL(2, F)).factorization r = (Fintype.card F).factorization r +
      (Fintype.card F - 1).factorization r + (Fintype.card F + 1).factorization r := by
    rw [card_SL2, Nat.factorization_mul (Nat.mul_ne_zero hq0 hqm) hqp,
      Nat.factorization_mul hq0 hqm]
    rfl
  have hq0' : (Fintype.card F).factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hrq
  have hcyc_SL : ∀ P : Sylow r SL(2, F), IsCyclic (P : Subgroup SL(2, F)) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨C, hC, hCc⟩ := exists_cyclic_sub_one F
      refine fun P => isCyclic_sylow_of_cyclic_subgroup C ?_ P
      rw [hSL, hCc, hq0', Nat.factorization_eq_zero_of_not_dvd h2]; simp
    · obtain ⟨C, hC, hCc⟩ := exists_cyclic_add_one F
      refine fun P => isCyclic_sylow_of_cyclic_subgroup C ?_ P
      rw [hSL, hCc, hq0', Nat.factorization_eq_zero_of_not_dvd h2]; simp
  intro P
  refine ⟨isCyclic_sylow_quotient (Subgroup.center SL(2, F)) hcyc_SL P, ?_⟩
  rw [Sylow.card_eq_multiplicity, factorization_card_PSL2 F hr2, hSL, hq0']
  have hpos : 0 < (Fintype.card F - 1).factorization r + (Fintype.card F + 1).factorization r := by
    rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := (Nat.Prime.dvd_iff_one_le_factorization hr.out hqm).mp h1; omega
    · have := (Nat.Prime.dvd_iff_one_le_factorization hr.out hqp).mp h1; omega
  intro h
  have := Nat.pow_right_injective hr.out.two_le (h.trans (pow_zero r).symm)
  omega

/-- For `|F| = 5`, the Sylow `5`-subgroups of `PSL(2, F)` have order `5`. -/
theorem psl2_five_sylow (h5 : Fintype.card F = 5) :
    ∀ P : Sylow 5 PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro P
  have hcard : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, factorization_card_PSL2 F (by norm_num), card_SL2, h5]
    have : (5 * (5 - 1) * (5 + 1) : ℕ) = 5 ^ 1 * 24 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num)]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 5 ∣ 24 by norm_num)]
  exact ⟨isCyclic_of_prime_card hcard, by rw [hcard]; norm_num⟩

end Sylow

section Primes

theorem exists_odd_prime_dvd {m : ℕ} (hm : Odd m) (h1 : 1 < m) : ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ m := by
  refine ⟨m.minFac, Nat.minFac_prime (by omega), fun h => ?_, Nat.minFac_dvd m⟩
  have h2 := Nat.minFac_dvd m
  rw [h] at h2
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

/-- A number `n > 4` with `n ≡ 2, 4, 6 (mod 8)` has an odd prime divisor. -/
theorem exists_odd_prime_dvd_of_mod {n : ℕ} (h8 : n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6) (hn : 4 < n) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ n := by
  rcases h8 with h | h | h
  · obtain ⟨r, hr, hr2, hrm⟩ := exists_odd_prime_dvd (m := n / 2) (Nat.odd_iff.mpr (by omega)) (by omega)
    exact ⟨r, hr, hr2, hrm.trans (Nat.div_dvd_of_dvd (by omega))⟩
  · obtain ⟨r, hr, hr2, hrm⟩ := exists_odd_prime_dvd (m := n / 4) (Nat.odd_iff.mpr (by omega)) (by omega)
    exact ⟨r, hr, hr2, hrm.trans (Nat.div_dvd_of_dvd (by omega))⟩
  · obtain ⟨r, hr, hr2, hrm⟩ := exists_odd_prime_dvd (m := n / 2) (Nat.odd_iff.mpr (by omega)) (by omega)
    exact ⟨r, hr, hr2, hrm.trans (Nat.div_dvd_of_dvd (by omega))⟩

theorem prime_eq_two_of_dvd_two {r : ℕ} (hr : r.Prime) (h : r ∣ 2) : r = 2 :=
  (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h

end Primes

section TwoPrimes

variable (F : Type) [Field F] [Fintype F]

/-- Odd primes `r ∣ q - 1` and `r' ∣ q + 1` both have nontrivial cyclic Sylow subgroups in `PSL(2, q)`. -/
theorem psl2_two_primes_of {r r' : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr' : r'.Prime) (hr'2 : r' ≠ 2)
    (h1 : r ∣ Fintype.card F - 1) (h2 : r' ∣ Fintype.card F + 1) :
    ∃ p r : ℕ, ∃ _ : Fact p.Prime, ∃ _ : Fact r.Prime, p ≠ r ∧
      (∀ P : Sylow p PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) ∧
      (∀ P : Sylow r PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have e1 : Fintype.card F + 1 = (Fintype.card F - 1) + 2 := by omega
  have e2 : Fintype.card F = (Fintype.card F - 1) + 1 := by omega
  haveI := Fact.mk hr
  haveI := Fact.mk hr'
  have hn1 : ¬ r ∣ Fintype.card F + 1 := fun h =>
    hr2 (prime_eq_two_of_dvd_two hr ((Nat.dvd_add_right h1).mp (e1 ▸ h)))
  have hn2 : ¬ r' ∣ Fintype.card F - 1 := fun h =>
    hr'2 (prime_eq_two_of_dvd_two hr' ((Nat.dvd_add_right h).mp (e1 ▸ h2)))
  have hq1 : ¬ r ∣ Fintype.card F := fun h =>
    hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp (e2 ▸ h)))
  have hq2 : ¬ r' ∣ Fintype.card F := fun h =>
    hr'.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h2))
  refine ⟨r, r', inferInstance, inferInstance, fun h => hn2 (h ▸ h1),
    psl2_cyclic_sylow F hr2 (Or.inl ⟨h1, hn1⟩) hq1, psl2_cyclic_sylow F hr'2 (Or.inr ⟨h2, hn2⟩) hq2⟩

/-- **The `PSL(2, q)` groups of Walter's list have two primes with nontrivial cyclic Sylow subgroups.** -/
theorem psl2_two_primes
    (hcase : (∃ f, 2 ≤ f ∧ Fintype.card F = 2 ^ f) ∨
      (Odd (Fintype.card F) ∧ 5 ≤ Fintype.card F ∧ (Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5))) :
    ∃ p r : ℕ, ∃ _ : Fact p.Prime, ∃ _ : Fact r.Prime, p ≠ r ∧
      (∀ P : Sylow p PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) ∧
      (∀ P : Sylow r PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) := by
  rcases hcase with ⟨f, hf, hq⟩ | ⟨hodd, h5, h8⟩
  · have h4 : 4 ≤ Fintype.card F := by
      rw [hq]; exact (Nat.pow_le_pow_right (by norm_num) hf : 2 ^ 2 ≤ 2 ^ f)
    have hev : (Fintype.card F) % 2 = 0 := by
      rw [hq]; exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨r, hr, hr2, h1⟩ := exists_odd_prime_dvd (m := Fintype.card F - 1)
      (Nat.odd_iff.mpr (by omega)) (by omega)
    obtain ⟨r', hr', hr'2, h2⟩ := exists_odd_prime_dvd (m := Fintype.card F + 1)
      (Nat.odd_iff.mpr (by omega)) (by omega)
    exact psl2_two_primes_of F hr hr2 hr' hr'2 h1 h2
  · by_cases hq5 : Fintype.card F = 5
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      refine ⟨3, 5, inferInstance, inferInstance, by norm_num, ?_, psl2_five_sylow F hq5⟩
      exact psl2_cyclic_sylow F (by norm_num) (Or.inr ⟨by rw [hq5]; norm_num, by rw [hq5]; norm_num⟩)
        (by rw [hq5]; norm_num)
    · obtain ⟨r, hr, hr2, h1⟩ := exists_odd_prime_dvd_of_mod (n := Fintype.card F - 1) (by omega) (by omega)
      obtain ⟨r', hr', hr'2, h2⟩ := exists_odd_prime_dvd_of_mod (n := Fintype.card F + 1) (by omega)
        (by omega)
      exact psl2_two_primes_of F hr hr2 hr' hr'2 h1 h2

end TwoPrimes

end

end CFSGOutside.Gagola
