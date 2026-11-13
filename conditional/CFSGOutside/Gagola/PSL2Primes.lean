import CFSGOutside.Gagola.PSL2Dihedral
import CFSGOutside.Corpus.SL2MinimalFaithfulZsigmondy

/-!
# Primes with cyclic Sylow subgroups in `PSL(2, p ^ f)`, and simplicity facts
-/

namespace CFSGOutside.Gagola

open Classical Matrix CFSGOutside.Corpus
open scoped MatrixGroups

noncomputable section

section Aux

theorem sq_sub_one_eq (n : ℕ) (hn : 1 ≤ n) : n ^ 2 - 1 = (n - 1) * (n + 1) := by
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  zify [hn, h1]
  ring

theorem n_dvd_pred_of_primitive {a n ℓ : ℕ} (hℓ : ℓ.Prime) (hn : 0 < n)
    (hdvd : ℓ ∣ a ^ n - 1) (hprim : ∀ k, 0 < k → k < n → ¬ ℓ ∣ a ^ k - 1) (ha : 1 ≤ a) :
    n ∣ ℓ - 1 := by
  haveI := Fact.mk hℓ
  have hpos : ∀ k, 1 ≤ a ^ k := fun k => Nat.one_le_pow _ _ ha
  have hcast : ∀ k, ℓ ∣ a ^ k - 1 ↔ ((a : ZMod ℓ)) ^ k = 1 := by
    intro k
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (hpos k), Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  have h1 : (a : ZMod ℓ) ^ n = 1 := (hcast n).mp hdvd
  have hne : (a : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  have hord : orderOf (a : ZMod ℓ) = n := by
    apply le_antisymm (orderOf_le_of_pow_eq_one hn h1)
    by_contra hlt
    push Not at hlt
    exact hprim _ (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h1⟩)) hlt
      ((hcast _).mpr (pow_orderOf_eq_one _))
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hne

theorem cyc_of_dvd (F : Type) [Field F] [Fintype F] {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (h : r ∣ Fintype.card F - 1 ∨ r ∣ Fintype.card F + 1) :
    ∀ P : Sylow r PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have e1 : Fintype.card F + 1 = (Fintype.card F - 1) + 2 := by omega
  have e2 : Fintype.card F = (Fintype.card F - 1) + 1 := by omega
  rcases h with h1 | h1
  · refine psl2_cyclic_sylow F hr2 (Or.inl ⟨h1, fun h => hr2 ?_⟩) (fun h => ?_)
    · exact prime_eq_two_of_dvd_two hr.out ((Nat.dvd_add_right h1).mp (e1 ▸ h))
    · exact hr.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp (e2 ▸ h)))
  · refine psl2_cyclic_sylow F hr2 (Or.inr ⟨h1, fun h => hr2 ?_⟩) (fun h => ?_)
    · exact prime_eq_two_of_dvd_two hr.out ((Nat.dvd_add_right h).mp (e1 ▸ h1))
    · exact hr.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp h1))

theorem exists_odd_prime_dvd_pm {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ (r ∣ m - 1 ∨ r ∣ m + 1) := by
  obtain ⟨k, hk⟩ := hm
  have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
  rcases this with h | h | h | h
  · obtain ⟨r, hr, hr2, hd⟩ := exists_odd_prime_dvd_of_mod (n := m + 1) (by omega) (by omega)
    exact ⟨r, hr, hr2, Or.inr hd⟩
  · obtain ⟨r, hr, hr2, hd⟩ := exists_odd_prime_dvd_of_mod (n := m + 1) (by omega) (by omega)
    exact ⟨r, hr, hr2, Or.inr hd⟩
  · obtain ⟨r, hr, hr2, hd⟩ := exists_odd_prime_dvd_of_mod (n := m + 1) (by omega) (by omega)
    exact ⟨r, hr, hr2, Or.inr hd⟩
  · obtain ⟨r, hr, hr2, hd⟩ := exists_odd_prime_dvd_of_mod (n := m - 1) (by omega) (by omega)
    exact ⟨r, hr, hr2, Or.inl hd⟩

theorem odd_not_dvd_of_not_dvd {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : ¬ r ∣ f) : ¬ r ∣ 4 * f := by
  intro hd
  rcases (Nat.Prime.dvd_mul hr).mp hd with h4 | h4
  · exact hr2 (prime_eq_two_of_dvd_two hr
      (by have : r ∣ 2 ^ 2 := by simpa using h4
          exact hr.dvd_of_dvd_pow this))
  · exact h h4

/-- Assemble the first alternative from odd primes `r₁ ∣ q + 1`, `r₂ ∣ q - 1` not dividing `f`. -/
theorem assemble (F : Type) [Field F] [Fintype F] (f : ℕ) {r₁ r₂ : ℕ} (h₁ : r₁.Prime) (h₂ : r₂.Prime)
    (h12 : r₁ ≠ 2) (h22 : r₂ ≠ 2) (hA : r₁ ∣ Fintype.card F + 1) (hB : r₂ ∣ Fintype.card F - 1)
    (hf1 : ¬ r₁ ∣ f) (hf2 : ¬ r₂ ∣ f) :
    ∃ r₁ r₂ : ℕ, ∃ _ : Fact r₁.Prime, ∃ _ : Fact r₂.Prime, r₁ ≠ r₂ ∧
        ¬ r₁ ∣ 4 * f ∧ ¬ r₂ ∣ 4 * f ∧
        (∀ P : Sylow r₁ PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) ∧
        (∀ P : Sylow r₂ PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) := by
  haveI := Fact.mk h₁
  haveI := Fact.mk h₂
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have e1 : Fintype.card F + 1 = (Fintype.card F - 1) + 2 := by omega
  refine ⟨r₁, r₂, inferInstance, inferInstance, ?_, odd_not_dvd_of_not_dvd h₁ h12 hf1,
    odd_not_dvd_of_not_dvd h₂ h22 hf2, cyc_of_dvd F h12 (Or.inr hA), cyc_of_dvd F h22 (Or.inl hB)⟩
  rintro rfl
  exact h12 (prime_eq_two_of_dvd_two h₁ ((Nat.dvd_add_right hB).mp (e1 ▸ hA)))

theorem psl2_nine (F : Type) [Field F] [Fintype F] (h : Fintype.card F = 9) :
    Nat.card PSL(2, F) = 360 ∧
      ∀ P : Sylow 5 PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P = 5 := by
  have hSL := card_SL2 F
  rw [h] at hSL
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  have hPSL : Nat.card PSL(2, F) = Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) := rfl
  rw [← hPSL] at hprod
  have hZle := card_center_le F
  have hZ : 2 ≤ Nat.card (Subgroup.center SL(2, F)) := by
    have hchar : ringChar F ≠ 2 := by
      intro hc
      have := (FiniteField.even_card_iff_char_two (F := F)).mp hc
      rw [h] at this
      exact absurd this (by decide)
    have hne : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hchar
    haveI : Fact (Even (Fintype.card (Fin 2))) := ⟨by simp⟩
    have hmem : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      ext i j
      simp
    have hnt : Nontrivial (Subgroup.center SL(2, F)) := by
      refine ⟨⟨⟨-1, hmem⟩, 1, ?_⟩⟩
      intro h1
      have h2 : (-1 : SL(2, F)) = 1 := congrArg Subtype.val h1
      have h3 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h2
      simp at h3
      exact hne h3
    exact Finite.one_lt_card_iff_nontrivial.mpr hnt
  refine ⟨?_, ?_⟩
  · rw [hSL] at hprod
    have : Nat.card (Subgroup.center SL(2, F)) = 2 := by omega
    rw [this] at hprod
    omega
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h5' : (Nat.card SL(2, F)).factorization 5 = 1 := by
      rw [hSL]
      have : (9 * (9 - 1) * (9 + 1) : ℕ) = 5 ^ 1 * 144 := by norm_num
      rw [this]
      exact vp_mul (by norm_num) 1 144 (by norm_num) (by norm_num)
    exact psl2_prime_sylow F (p := 5) (by norm_num) h5'


theorem not_dvd_pred_succ {p : ℕ} (hp : 2 ≤ p) : ¬ p ∣ p - 1 ∧ ¬ p ∣ p + 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := Nat.le_of_dvd (by omega) h
    omega
  · have := (Nat.dvd_add_right (dvd_refl p)).mp h
    have := Nat.le_of_dvd (by omega) this
    omega

theorem sq_mod_eight {p : ℕ} (hp : Odd p) : p ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ := hp
  have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]

end Aux

/-- **Primes for `PSL(2, p ^ f)`** (`p ^ f` odd, `≥ 5`): two primes not dividing `4 f` with nontrivial cyclic
Sylow subgroups, except for `q = 9`. Uses Zsigmondy's theorem (corpus class) for `f ≥ 3`. -/
theorem psl2_prime_choice [SL2MinimalFaithfulZsigmondy]
    (F : Type) [Field F] [Fintype F] (p f : ℕ) [Fact p.Prime]
    (hF : Fintype.card F = p ^ f) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (h5 : 5 ≤ p ^ f) :
    (∃ r₁ r₂ : ℕ, ∃ _ : Fact r₁.Prime, ∃ _ : Fact r₂.Prime, r₁ ≠ r₂ ∧
        ¬ r₁ ∣ 4 * f ∧ ¬ r₂ ∣ 4 * f ∧
        (∀ P : Sylow r₁ PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1) ∧
        (∀ P : Sylow r₂ PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P ≠ 1)) ∨
    (p ^ f = 9 ∧ Nat.card PSL(2, F) = 360 ∧ ¬ 5 ∣ 4 * f ∧
        ∀ P : Sylow 5 PSL(2, F), IsCyclic (P : Subgroup PSL(2, F)) ∧ Nat.card P = 5) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h
      exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))
    · exact h
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hpodd
    have := hp.two_le
    omega
  have hcases : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
  rcases hcases with h1 | h2 | h3
  · subst h1
    rw [pow_one] at hF h5 hodd
    left
    obtain ⟨r, hr, hr2, hd⟩ := exists_odd_prime_dvd_pm (m := p) hodd h5
    haveI := Fact.mk hr
    have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have hnd := not_dvd_pred_succ hp.two_le
    refine ⟨p, r, inferInstance, inferInstance, ?_, ?_, odd_not_dvd_of_not_dvd hr hr2 hr.not_dvd_one,
      ?_, cyc_of_dvd F hr2 (by rwa [hF])⟩
    · rintro rfl
      rcases hd with hd | hd
      · exact hnd.1 hd
      · exact hnd.2 hd
    · intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · intro P
      have hv : (Nat.card SL(2, F)).factorization p = 1 := by
        rw [card_SL2, hF]
        have e : p * (p - 1) * (p + 1) = p ^ 1 * ((p - 1) * (p + 1)) := by ring
        rw [e]
        refine vp_mul hp 1 _ ?_ (Nat.mul_ne_zero (by omega) (by omega))
        intro hd'
        rcases (Nat.Prime.dvd_mul hp).mp hd' with h | h
        · exact hnd.1 h
        · exact hnd.2 h
      obtain ⟨c, hc⟩ := psl2_prime_sylow F (p := p) (by omega) hv P
      exact ⟨c, by rw [hc]; exact hp.one_lt.ne'⟩
  · subst h2
    by_cases h3 : p = 3
    · subst h3
      right
      have h9 : Fintype.card F = 9 := by rw [hF]; norm_num
      obtain ⟨hc, hs⟩ := psl2_nine F h9
      exact ⟨by norm_num, hc, by norm_num, hs⟩
    · left
      have hp5 : 5 ≤ p := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      obtain ⟨r₁, hr₁, hr₁2, hd₁⟩ := exists_odd_prime_dvd_of_mod (n := p ^ 2 + 1)
        (by have := sq_mod_eight hpodd; omega) (by nlinarith)
      obtain ⟨r₂, hr₂, hr₂2, hd₂⟩ := exists_odd_prime_dvd_pm (m := p) hpodd hp5
      refine assemble F 2 hr₁ hr₂ hr₁2 hr₂2 (by rw [hF]; exact hd₁) ?_
        (fun h => hr₁2 (prime_eq_two_of_dvd_two hr₁ h))
        (fun h => hr₂2 (prime_eq_two_of_dvd_two hr₂ h))
      rw [hF, sq_sub_one_eq p (by omega)]
      rcases hd₂ with h | h
      · exact h.mul_right _
      · exact h.mul_left _
  · left
    have hq1 : 1 ≤ p ^ f := by omega
    obtain ⟨l1, hl1, hd1, hpr1⟩ :=
      SL2MinimalFaithfulZsigmondy.exists_primitive_prime_dvd_pow_sub_one (a := p) (n := 2 * f) hp3
        (by omega)
    obtain ⟨l2, hl2, hd2, hpr2⟩ :=
      SL2MinimalFaithfulZsigmondy.exists_primitive_prime_dvd_pow_sub_one (a := p) (n := f) hp3 h3
    have o1 := n_dvd_pred_of_primitive hl1 (by omega) hd1 hpr1 (by omega)
    have o2 := n_dvd_pred_of_primitive hl2 (by omega) hd2 hpr2 (by omega)
    have hl1p := hl1.two_le
    have hl2p := hl2.two_le
    have b1 : 2 * f ≤ l1 - 1 := Nat.le_of_dvd (by omega) o1
    have b2 : f ≤ l2 - 1 := Nat.le_of_dvd (by omega) o2
    have hsq : p ^ (2 * f) - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      rw [pow_mul', sq_sub_one_eq _ hq1]
    have hnd1 : ¬ l1 ∣ p ^ f - 1 := hpr1 f (by omega) (by omega)
    have hA : l1 ∣ p ^ f + 1 := by
      rw [hsq] at hd1
      rcases (Nat.Prime.dvd_mul hl1).mp hd1 with h | h
      · exact absurd h hnd1
      · exact h
    have hf1 : ¬ l1 ∣ f := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    have hf2 : ¬ l2 ∣ f := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    exact assemble F f hl1 hl2 (by omega) (by omega) (by rw [hF]; exact hA) (by rw [hF]; exact hd2)
      hf1 hf2

section Simple

theorem not_comm_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => hc a b }
  exact h (IsSimpleGroup.prime_card (α := G))

theorem isSimpleGroup_psl2 (F : Type) [Field F] [Fintype F] (h : 4 ≤ Fintype.card F) :
    IsSimpleGroup PSL(2, F) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rwa [Nat.card_eq_fintype_card])

theorem isSimpleGroup_alt7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem not_comm_psl2 (F : Type) [Field F] [Fintype F] (h : 4 ≤ Fintype.card F) :
    ∃ a b : PSL(2, F), a * b ≠ b * a := by
  haveI := isSimpleGroup_psl2 F h
  refine not_comm_of_simple fun hpr => ?_
  have hSL := card_SL2 F
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, F))
  have hPSL : Nat.card PSL(2, F) = Nat.card (SL(2, F) ⧸ Subgroup.center SL(2, F)) := rfl
  rw [← hPSL] at hprod
  have hZle := card_center_le F
  have hZpos : 0 < Nat.card (Subgroup.center SL(2, F)) := Nat.card_pos
  set q := Fintype.card F with hq
  set N := Nat.card PSL(2, F) with hN
  have hdvd : N ∣ q * (q - 1) * (q + 1) := by
    rw [← hSL, hprod]; exact dvd_mul_right _ _
  have hle : N ≤ q + 1 := by
    rcases (Nat.Prime.dvd_mul hpr).mp hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpr).mp h1 with h2 | h2
      · exact (Nat.le_of_dvd (by omega) h2).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h2).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h1
  rw [hSL] at hprod
  have h2 : q * (q - 1) * (q + 1) ≤ 2 * (q + 1) := by
    rw [hprod]
    exact Nat.mul_le_mul (by omega) hZle |>.trans (by omega)
  have h3 : q * (q - 1) ≤ 2 := Nat.le_of_mul_le_mul_right h2 (by omega)
  have : 4 * 3 ≤ q * (q - 1) := Nat.mul_le_mul h (by omega)
  omega

theorem not_comm_alt7 : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
  haveI := isSimpleGroup_alt7
  refine not_comm_of_simple fun hpr => ?_
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [hcard] at hpr
  norm_num at hpr

theorem sylow5_alt7 : ∀ P : Sylow 5 (alternatingGroup (Fin 7)),
    IsCyclic (P : Subgroup (alternatingGroup (Fin 7))) ∧ Nat.card P ≠ 1 ∧
      (Nat.card P).factorial < Nat.card (alternatingGroup (Fin 7)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro P
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    have : (2520 : ℕ) = 5 ^ 1 * 504 := by norm_num
    rw [this, vp_mul (by norm_num) 1 504 (by norm_num) (by norm_num), pow_one]
  refine ⟨isCyclic_of_prime_card hP, by rw [hP]; norm_num, ?_⟩
  rw [hP, hcard]
  decide

end Simple

end

end CFSGOutside.Gagola
