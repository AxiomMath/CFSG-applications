import CFSGOutside.Corpus.DicksonPsl2
import CFSGOutside.GaloisMinimalDegree.Basic
import CFSGOutside.GaloisMinimalDegree.Pgl

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

open CFSGOutside.Corpus CFSGOutside.Psl2Basic

lemma card_sl2 (F : Type) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F * Nat.card F - 1) := by
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field 2, ← Nat.card_eq_fintype_card (α := F)]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at *
  simp only [Fin.prod_univ_two, pow_zero, Fin.val_zero, Fin.val_one, pow_one]
  have h1 : 1 ≤ q * q := by nlinarith
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : 1 ≤ q ^ 2 := by nlinarith
  have e : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q * q - 1) * (q - 1) := by
    zify [h1, h2, h3, (by omega : 1 ≤ q)]
    ring
  rw [e]
  exact Nat.mul_div_cancel _ (by omega)

lemma card_center_le (F : Type) [Field F] [Finite F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
      Nat.gcd (Nat.card F - 1) 2 := by
  classical
  have := Fintype.ofFinite F
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 2) (R := F) 0
  rw [Nat.card_congr e.toEquiv]
  let T : Finset F := {1, -1}
  have hmem : ∀ u : rootsOfUnity (Fintype.card (Fin 2)) F, ((u : Fˣ) : F) ∈ T := by
    intro u
    have hu : (u : Fˣ) ^ 2 = 1 := by simpa using (mem_rootsOfUnity _ _).1 u.2
    have h2 : ((u : Fˣ) : F) ^ 2 = 1 := by
      have := congrArg Units.val hu
      simpa using this
    have h3 : (((u : Fˣ) : F) - 1) * (((u : Fˣ) : F) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [T, sub_eq_zero.1 h]
    · simp [T, eq_neg_of_add_eq_zero_left h]
  have hinj : Function.Injective
      (fun u : rootsOfUnity (Fintype.card (Fin 2)) F => (⟨((u : Fˣ) : F), hmem u⟩ : T)) := by
    intro a b hab
    have : ((a : Fˣ) : F) = ((b : Fˣ) : F) := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext this)
  have h1 : Nat.card (rootsOfUnity (Fintype.card (Fin 2)) F) ≤ T.card := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_eq_fintype_card] using this
  refine h1.trans ?_
  by_cases hev : Even (Fintype.card F)
  · have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 hev)
    haveI : CharP F 2 := ringChar.of_eq hc
    have hT : T.card = 1 := by
      simp [T, CharTwo.neg_eq]
    have hg : Nat.gcd (Nat.card F - 1) 2 = 1 := by
      rw [Nat.card_eq_fintype_card, Nat.gcd_comm, Nat.gcd_rec]
      obtain ⟨k, hk⟩ := hev
      have : Fintype.card F ≠ 0 := Fintype.card_ne_zero
      have : (Fintype.card F - 1) % 2 = 1 := by omega
      simp [this]
    omega
  · have hT : T.card ≤ 2 := Finset.card_le_two
    have hg : Nat.gcd (Nat.card F - 1) 2 = 2 := by
      rw [Nat.card_eq_fintype_card, Nat.gcd_comm, Nat.gcd_rec]
      have : (Fintype.card F - 1) % 2 = 0 := by
        rw [Nat.not_even_iff_odd] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      simp [this]
    omega

lemma ell_eq_of_elementary {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    (h : IsElementaryAbelian p G) : ∃ k, Nat.card G = p ^ k := by
  haveI := Fact.mk hp
  have : IsPGroup p G := fun g => ⟨1, by
    have h1 : orderOf g ∣ p := (Monoid.order_dvd_exponent g).trans h.exponent_dvd_p
    simpa using orderOf_dvd_iff_pow_eq_one.1 h1⟩
  exact this.exists_card_eq

set_option maxHeartbeats 2000000 in
theorem galois_minimal_degree [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hne : H ≠ ⊤)
    (hidx : H.index ≤ Nat.card F) :
    Nat.card F = 2 ∨ Nat.card F = 3 ∨ Nat.card F = 5 ∨ Nat.card F = 7 ∨
      Nat.card F = 9 ∨ Nat.card F = 11 := by
  have hp := (inferInstance : Fact p.Prime).out
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hD := DicksonPsl2SubgroupClassification.huppert_II_8_27_dickson_psl2_subgroup_classification hF H
  have hSL := card_sl2 F
  have hZle := card_center_le F
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
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hF
    omega
  have hpq : p ∣ Nat.card F := by rw [hF]; exact dvd_pow_self p hf
  have hpf : p ^ f = Nat.card F := hF.symm
  have hsq : p ^ (2 * f) = Nat.card F * Nat.card F := by rw [pow_mul', hpf, sq]
  have hFC := hF
  obtain ⟨N, hNdef⟩ : ∃ N, N = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.card H := ⟨_, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, i = H.index := ⟨_, rfl⟩
  obtain ⟨z0, hz0⟩ : ∃ z0, z0 = Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    ⟨_, rfl⟩
  rw [← hNdef, ← hz0] at hNmul
  rw [← hn, ← hi, ← hNdef] at hHN
  rw [← hNdef, ← hn] at hdvdN
  rw [← hi] at hi1 hi0 hidx
  rw [← hz0] at hZle
  have hH' : H ≠ ⊤ := hne
  generalize hq : Nat.card F = q at *
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd (q - 1) 2 := ⟨_, rfl⟩
  rw [← hd] at hZle
  have hd2 : d ≤ 2 := hd ▸ Nat.gcd_le_right _ (by norm_num)
  have hd1 : 1 ≤ d := hd ▸ Nat.gcd_pos_of_pos_right _ (by norm_num)
  have hdq1 : d * ((q - 1) / d) = q - 1 := Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_left _ _)
  have hdq2 : d * ((q + 1) / d) = q + 1 := by
    apply Nat.mul_div_cancel'
    have h1 : d ∣ q - 1 := hd ▸ Nat.gcd_dvd_left _ _
    have h2 : d ∣ 2 := hd ▸ Nat.gcd_dvd_right _ _
    have := Nat.dvd_add h1 h2
    rwa [show q - 1 + 2 = q + 1 by omega] at this
  obtain ⟨s, hs⟩ : ∃ s, s = q * q - 1 := ⟨_, rfl⟩
  have hs1 : s + 1 = q * q := by
    have : 1 ≤ q * q := by nlinarith
    omega
  rw [← hs] at hSL
  have hNqs : N * z0 = q * s := by rw [← hSL, hNmul]
  have hNle : N ≤ q * s := by
    have hz : 1 ≤ z0 := by
      rw [hz0]; exact Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    nlinarith
  have hE : s ≤ d * n := by
    have h1 : q * s ≤ d * N := by
      calc q * s = N * z0 := hNqs.symm
        _ ≤ N * d := Nat.mul_le_mul_left _ hZle
        _ = d * N := Nat.mul_comm _ _
    have h2 : d * N ≤ d * (n * q) := by
      rw [← hHN]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hidx)
    have h3 : q * s ≤ q * (d * n) := by
      calc q * s ≤ d * (n * q) := h1.trans h2
        _ = q * (d * n) := by ring
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  have hE' : q * q ≤ d * n + 1 := by omega
  have hnpos : 0 < n := by rw [hn]; exact Nat.card_pos
  have hu1 : 0 < (q - 1) / d := Nat.div_pos (hd ▸ Nat.gcd_le_left _ (by omega)) (by omega)
  have hu2 : 0 < (q + 1) / d := Nat.div_pos (by omega) (by omega)
  have hbig : 2 * n ≤ q * s := by
    have : 2 * n ≤ n * i := by
      have : 2 ≤ i := by omega
      nlinarith
    calc 2 * n ≤ n * i := this
      _ = N := hHN
      _ ≤ q * s := hNle
  have hNdvd : N ∣ q * s := ⟨z0, hNqs.symm⟩
  have hps : ¬ p ∣ s := by
    intro h
    have h1 : p ∣ q * q := (hpq.mul_right q)
    have h2 : p ∣ 1 := by
      have := Nat.dvd_sub h1 h
      rwa [← hs1, Nat.add_sub_cancel_left] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hpp : ∀ k, p ^ k ∣ n → p ^ k ≤ q := by
    intro k hk
    have h1 : p ^ k ∣ q * s := (hk.trans hdvdN).trans hNdvd
    have hco : Nat.Coprime (p ^ k) s :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hps)
    exact Nat.le_of_dvd (by omega) (hco.dvd_of_dvd_mul_right h1)
  suffices key : q ≤ 11 ∧ q ≠ 4 ∧ q ≠ 8 by
    obtain ⟨k1, k2, k3⟩ := key
    have hf4 : f < 4 := by
      by_contra h
      push Not at h
      have : 2 ^ 4 ≤ p ^ f :=
        (Nat.pow_le_pow_right (by norm_num) h).trans (Nat.pow_le_pow_left hp.two_le f)
      omega
    have hp11 : p ≤ 11 := by
      have : p ≤ p ^ f := Nat.le_self_pow hf p
      omega
    have hpf' : p ^ f = q := hpf
    interval_cases f <;> interval_cases p <;> first | omega | (exfalso; norm_num at hp)
  rcases hD with
    hel | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz, hcard, ⟨hdih⟩⟩ | ⟨-, ⟨hA4⟩⟩ | ⟨h16, ⟨hS4⟩⟩ |
    ⟨h5, ⟨hA5⟩⟩ | ⟨m, t, ht1, ht2, N', C, hN', hNe, hNc, hC, hCc, hdisj, hsup⟩ |
    ⟨m, hm0, hmf, ⟨φ⟩⟩ | ⟨m, hm0, hmf2, ⟨φ⟩⟩
  · obtain ⟨k, hk⟩ := ell_eq_of_elementary hp hel
    have hk' : n = p ^ k := hn.trans hk
    have hnq : n ≤ q := by rw [hk']; exact hpp k (dvd_of_eq hk'.symm)
    have : q ≤ 2 := by nlinarith
    omega
  · rw [← hd] at hz
    rw [← hn] at hcard
    have hzp : 0 < z := by omega
    have : d * z ≤ q + 1 := by
      rcases hz with hz | hz
      · have := Nat.mul_le_mul_left d (Nat.le_of_dvd hu1 hz)
        omega
      · have := Nat.mul_le_mul_left d (Nat.le_of_dvd hu2 hz)
        omega
    have : q ≤ 2 := by rw [hcard] at hE'; nlinarith
    omega
  · rw [← hd] at hz
    rw [← hn] at hcard
    have hzp : 0 < z := by omega
    have : d * z ≤ q + 1 := by
      rcases hz with hz | hz
      · have := Nat.mul_le_mul_left d (Nat.le_of_dvd hu1 hz)
        omega
      · have := Nat.mul_le_mul_left d (Nat.le_of_dvd hu2 hz)
        omega
    have : q ≤ 3 := by rw [hcard] at hE'; nlinarith
    omega
  · have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl
    have : n = 12 := by rw [hn, Nat.card_congr hA4.toEquiv, hc]
    have hq5 : q ≤ 5 := by subst this; nlinarith
    have : q ≠ 4 := by
      rintro rfl
      have : d = 1 := by rw [hd]; norm_num
      subst this; omega
    omega
  · have hc : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
    have : n = 24 := by rw [hn, Nat.card_congr hS4.toEquiv, hc]
    have hq7 : q ≤ 7 := by subst this; nlinarith
    rw [hsq] at h16
    interval_cases q <;> omega
  · have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; rfl
    have hn60 : n = 60 := by rw [hn, Nat.card_congr hA5.toEquiv, hc]
    have hq11 : q ≤ 11 := by subst hn60; nlinarith
    refine ⟨hq11, ?_, ?_⟩
    · rintro rfl
      subst hn60
      have : s = 15 := by omega
      subst this
      omega
    · rintro rfl
      rcases h5 with h5 | h5
      · subst h5; omega
      · rw [hsq] at h5; omega
  · exfalso
    rw [hpf, ← hd] at ht2
    have hcompl : Subgroup.IsComplement' N' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
        rw [← Subgroup.normal_mul, hsup]; simp)
    have hmul := hcompl.card_mul
    rw [hNc, hCc] at hmul
    have hnm : n = p ^ m * t := by rw [hn, ← hmul]
    have hpm : p ^ m ≤ q := hpp m (by rw [hnm]; exact dvd_mul_right _ _)
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hnm; omega
      · exact h
    have htle : d * t ≤ q - 1 := by
      have := Nat.le_of_dvd (by omega) ht2
      have := Nat.mul_le_mul_left d this
      omega
    have : d * n ≤ q * (q - 1) := by
      rw [hnm]
      calc d * (p ^ m * t) = p ^ m * (d * t) := by ring
        _ ≤ q * (q - 1) := Nat.mul_le_mul hpm htle
    have hq1 : q * (q - 1) + q = q * q := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp; ring
    omega
  · by_cases hmeq : m = f
    · exfalso
      subst hmeq
      have := Fintype.ofFinite F
      have := Fintype.ofFinite (GaloisField p m)
      have e : F ≃+* GaloisField p m := FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hq, hF,
          GaloisField.card p m hm0])
      exact hH' (eq_top_of_equiv_psl2 e H φ)
    · exfalso
      have h2m : 2 * m ≤ f := by
        obtain ⟨c, rfl⟩ := hmf
        rcases c with _ | _ | c
        · omega
        · omega
        · nlinarith
      have := Fintype.ofFinite (GaloisField p m)
      have hcq : Nat.card (GaloisField p m) = p ^ m := by
        exact GaloisField.card p m hm0
      have hqq : p ^ m * p ^ m ≤ q := by
        rw [← hpf, ← pow_add]
        exact Nat.pow_le_pow_right hp.pos (by omega)
      have hSL' := card_sl2 (GaloisField p m)
      rw [hcq] at hSL'
      have hdv : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) ∣
          Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) :=
        ⟨Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m))), by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _)]⟩
      have hnle : n ≤ p ^ m * (p ^ m * p ^ m - 1) := by
        rw [hn, Nat.card_congr φ.toEquiv, ← hSL']
        exact Nat.le_of_dvd Nat.card_pos hdv
      have ha : 2 ≤ p ^ m := (hp.two_le).trans (Nat.le_self_pow hm0 p)
      generalize p ^ m = a at *
      obtain ⟨s', hs'⟩ : ∃ s', s' + 1 = a * a := ⟨a * a - 1, by have := Nat.mul_le_mul ha ha; omega⟩
      have : a * a - 1 = s' := by omega
      rw [this] at hnle
      have hqq2 : (a * a) * (a * a) ≤ q * q := Nat.mul_le_mul hqq hqq
      have h1 : d * n ≤ 2 * (a * s') := Nat.mul_le_mul hd2 hnle
      rw [← hs'] at hqq2
      have h2 : s' * (s' + 2) ≤ s' * (2 * a) := by nlinarith
      have h3 : s' + 2 ≤ 2 * a := Nat.le_of_mul_le_mul_left h2 (by
        have := Nat.mul_le_mul ha ha; omega)
      have := Nat.mul_le_mul_right a ha
      omega
  · exfalso
    have h2m : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf) hmf2
    have := Fintype.ofFinite (GaloisField p m)
    have hcq : Nat.card (GaloisField p m) = p ^ m := by
      exact GaloisField.card p m hm0
    have hqq : p ^ m * p ^ m ≤ q := by
      rw [← hpf, ← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    have hnle : n ≤ p ^ m * (p ^ m * p ^ m - 1) := by
      have := card_pgl2_le (GaloisField p m)
      rw [hcq] at this
      rw [hn, Nat.card_congr φ.toEquiv]
      exact this
    have ha : 2 ≤ p ^ m := (hp.two_le).trans (Nat.le_self_pow hm0 p)
    generalize p ^ m = a at *
    obtain ⟨s', hs'⟩ : ∃ s', s' + 1 = a * a := ⟨a * a - 1, by have := Nat.mul_le_mul ha ha; omega⟩
    have : a * a - 1 = s' := by omega
    rw [this] at hnle
    have hqq2 : (a * a) * (a * a) ≤ q * q := Nat.mul_le_mul hqq hqq
    have h1 : d * n ≤ 2 * (a * s') := Nat.mul_le_mul hd2 hnle
    rw [← hs'] at hqq2
    have h2 : s' * (s' + 2) ≤ s' * (2 * a) := by nlinarith
    have h3 : s' + 2 ≤ 2 * a := Nat.le_of_mul_le_mul_left h2 (by
      have := Nat.mul_le_mul ha ha; omega)
    have := Nat.mul_le_mul_right a ha
    omega

end CFSGOutside.GaloisMinimalDegree
