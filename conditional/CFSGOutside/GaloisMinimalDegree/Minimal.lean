import CFSGOutside.GaloisMinimalDegree.Main

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

open CFSGOutside.Corpus CFSGOutside.Psl2Basic

lemma card_center_eq_two (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  have := Fintype.ofFinite F
  have hle := card_center_le F
  have hg : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.gcd_comm, Nat.gcd_rec]
    have : (2 * k + 1 - 1) % 2 = 0 := by omega
    simp [this]
  rw [hg] at hle
  have hne : (-1 : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h00
    have h2 : (2 : F) = 0 := by linear_combination -h00
    have hdv : ringChar F ∣ 2 := by
      haveI := ringChar.charP F
      exact (CharP.cast_eq_zero_iff F (ringChar F) 2).1 (by exact_mod_cast h2)
    have hch : ringChar F = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdv with h | h
      · exact absurd h (CharP.ringChar_ne_one)
      · exact h
    have hev := FiniteField.even_card_iff_char_two.1 hch
    have hodd' := Nat.odd_iff.1 hodd
    rw [Nat.card_eq_fintype_card] at hodd'
    omega
  let A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨-1, by simp [Matrix.det_neg]⟩
  have hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) F) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) F)
    simp
  have hA1 : A ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have : 1 < Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    haveI : Nontrivial (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      ⟨⟨⟨A, hA⟩, 1, fun h => hA1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  omega

set_option maxHeartbeats 4000000 in
theorem no_smaller_index [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp5 : p = 5 ∨ p = 7 ∨ p = 11)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hne : H ≠ ⊤)
    (hlt : H.index < p) : False := by
  have hp := (inferInstance : Fact p.Prime).out
  have hodd : Odd (Nat.card F) := by
    rw [hF]; rcases hp5 with rfl | rfl | rfl <;> decide
  have hF1 : Nat.card F = p ^ 1 := by rw [hF, pow_one]
  have hD := DicksonPsl2SubgroupClassification.huppert_II_8_27_dickson_psl2_subgroup_classification hF1 H
  have hSL := card_sl2 F
  have hz0 := card_center_eq_two F hodd
  have hNmul : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hHN : Nat.card H * H.index = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Subgroup.card_mul_index H
  have hi1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdvdN : Nat.card H ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Subgroup.card_subgroup_dvd_card H
  have hd : Nat.gcd (p - 1) 2 = 2 := by
    rcases hp5 with rfl | rfl | rfl <;> norm_num
  rw [hF] at hSL hD
  simp only [pow_one] at hD
  rw [hz0, hSL] at hNmul
  obtain ⟨N, hNdef⟩ : ∃ N, N = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.card H := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, i = H.index := ⟨_, rfl⟩
  rw [← hNdef] at hNmul hHN hdvdN
  rw [← hn, ← hi] at hHN
  rw [← hn] at hdvdN
  rw [← hi] at hi1 hi0 hlt
  rw [hd] at hD
  have hsq : p * p - 1 + 1 = p * p := by
    have : 1 ≤ p * p := by nlinarith [hp.two_le]
    omega
  have hps : ¬ p ∣ p * p - 1 := by
    intro h
    have h1 : p ∣ p * p := Dvd.intro _ rfl
    have h2 : p ∣ 1 := by
      have := Nat.dvd_sub h1 h
      rwa [show p * p - (p * p - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hNdvd : N ∣ p * (p * p - 1) := ⟨2, hNmul⟩
  have hpp : ∀ k, p ^ k ∣ n → p ^ k ≤ p := by
    intro k hk
    have h1 : p ^ k ∣ p * (p * p - 1) := (hk.trans hdvdN).trans hNdvd
    have hco : Nat.Coprime (p ^ k) (p * p - 1) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hps)
    exact Nat.le_of_dvd hp.pos (hco.dvd_of_dvd_mul_right h1)
  have hp2 := hp.two_le
  have hbound : ∀ z : ℕ, (z ∣ (p - 1) / 2 ∨ z ∣ (p + 1) / 2) → 2 * z ≤ p + 1 := by
    intro z hz
    have : 0 < (p - 1) / 2 := by rcases hp5 with rfl | rfl | rfl <;> norm_num
    rcases hz with hz | hz
    · have := Nat.le_of_dvd this hz; omega
    · have := Nat.le_of_dvd (by omega) hz; omega
  have hfinish : ∀ B : ℕ, n ≤ B → B ≤ p + 1 → False := by
    intro B hnB hB
    rcases hp5 with rfl | rfl | rfl <;> nlinarith
  rcases hD with
    hel | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz, hcard, ⟨hdih⟩⟩ | ⟨-, ⟨hA4⟩⟩ | ⟨h16, ⟨hS4⟩⟩ |
    ⟨h5, ⟨hA5⟩⟩ | ⟨m, t, ht1, ht2, N', C, hN', hNe, hNc, hC, hCc, hdisj, hsup⟩ |
    ⟨m, hm0, hmf, ⟨φ⟩⟩ | ⟨m, hm0, hmf2, ⟨φ⟩⟩
  · obtain ⟨k, hk⟩ := ell_eq_of_elementary hp hel
    have hk' : n = p ^ k := hn.trans hk
    have hnq : n ≤ p := by rw [hk']; exact hpp k (dvd_of_eq hk'.symm)
    exact hfinish p hnq (by omega)
  · have := hbound z hz
    exact hfinish z (by omega) (by omega)
  · have := hbound z hz
    exact hfinish (p + 1) (by omega) le_rfl
  · have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl
    have : n = 12 := by rw [hn, Nat.card_congr hA4.toEquiv, hc]
    subst this
    rcases hp5 with rfl | rfl | rfl <;> omega
  · have hc : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
    have : n = 24 := by rw [hn, Nat.card_congr hS4.toEquiv, hc]
    subst this
    rcases hp5 with rfl | rfl | rfl <;> omega
  · have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl
    have : n = 60 := by rw [hn, Nat.card_congr hA5.toEquiv, hc]
    subst this
    rcases hp5 with rfl | rfl | rfl <;> omega
  · have hcompl : Subgroup.IsComplement' N' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
        rw [← Subgroup.normal_mul, hsup]; simp)
    have hmul := hcompl.card_mul
    rw [hNc, hCc] at hmul
    have hnm : n = p ^ m * t := by rw [hn, ← hmul]
    have hpm : p ^ m ≤ p := hpp m (by rw [hnm]; exact dvd_mul_right _ _)
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · have : 0 < n := hn ▸ Nat.card_pos
        rw [h] at hnm; simp at hnm; omega
      · exact h
    have htle : 2 * t ≤ p - 1 := by
      have := Nat.le_of_dvd (by rcases hp5 with rfl | rfl | rfl <;> norm_num) ht2
      omega
    have : 2 * n ≤ p * (p - 1) := by
      rw [hnm]
      calc 2 * (p ^ m * t) = p ^ m * (2 * t) := by ring
        _ ≤ p * (p - 1) := Nat.mul_le_mul hpm htle
    rcases hp5 with rfl | rfl | rfl <;> nlinarith
  · exfalso
    have hm1 : m = 1 := Nat.dvd_one.1 hmf
    subst hm1
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p 1)
    have e : F ≃+* GaloisField p 1 := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p 1 hm0, pow_one])
    exact hne (eq_top_of_equiv_psl2 e H φ)
  · exfalso
    have := Nat.le_of_dvd (by norm_num) hmf2
    omega

end CFSGOutside.GaloisMinimalDegree
