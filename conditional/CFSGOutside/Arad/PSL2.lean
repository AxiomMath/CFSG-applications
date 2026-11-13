import CFSGOutside.Arad.Defs
import CFSGOutside.Arad.PSL2Aux

/-!
# Arad, Theorem B(iii): `PSL(2, F)` is not π-homogeneous

For a finite field `F` with `|F| ≥ 4` and a set `π` of primes with `2 ∉ π`, every prime `p ∈ π` dividing
`|PSL(2, F)|` yields a nonidentity `r`-subgroup (`r ∈ π`) normalized but not centralized by an `s`-element
(`s ∉ π`). This is Arad's Lemma 2.1 for `PSL(2, q)`, proved here without the subgroup structure of `PSL(2, q)`.
-/

open scoped MatrixGroups

namespace CFSGOutside.Arad

/-- Lemma 2.1 of Arad (1974) for `PSL(2, q)`, `q ≥ 4`, in the form used by the proof of Theorem B(iii). -/
theorem modelBad_psl (F : Type*) [Field F] [Finite F] (hF : 4 ≤ Nat.card F) : ModelBad PSL(2, F) := by
  haveI := Fintype.ofFinite F
  intro π h2 p hp hpπ hpd
  have hp2 : p ≠ 2 := fun h => h2 (h ▸ hpπ)
  by_cases hpc : p = ringChar F
  · have hc2 : ringChar F ≠ 2 := hpc ▸ hp2
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc2
    by_cases hq : Fintype.card F % 4 = 3
    · -- `q ≡ 3 (mod 4)`: use an odd prime divisor `s` of `(q - 1) / 2`
      have hq4 : 4 ≤ Fintype.card F := by simpa [Nat.card_eq_fintype_card] using hF
      obtain ⟨N, hN⟩ : ∃ N, Fintype.card F = 2 * N + 1 := ⟨(Fintype.card F - 1) / 2, by omega⟩
      have hN3 : N % 2 = 1 := by omega
      have hN1 : N ≠ 1 := by omega
      have hs : (Nat.minFac N).Prime := Nat.minFac_prime hN1
      set s := Nat.minFac N with hs_def
      have hsN : s ∣ N := Nat.minFac_dvd N
      have hs2 : s ≠ 2 := by
        rintro h
        rw [h] at hsN; omega
      have hsq : s ∣ Fintype.card F - 1 := hsN.trans ⟨2, by omega⟩
      haveI := Fact.mk hs
      obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) s
        (by rw [Nat.card_units, ← Nat.card_eq_fintype_card] at *; simpa [Nat.card_eq_fintype_card] using hsq)
      have hdd : d ^ 2 ≠ 1 := by
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hd] at this
        exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp this)
      have hds : (d ^ s ^ 1) ^ 2 = 1 := by
        rw [pow_one, ← hd, pow_orderOf_eq_one, one_pow]
      by_cases hsπ : s ∈ π
      · have hsc : s ≠ ringChar F := by
          intro h
          have hq0 : ringChar F ∣ Fintype.card F :=
            (ringChar.spec F _).mp (FiniteField.cast_card_eq_zero F)
          have h1 : s ∣ (Fintype.card F - 1) + 1 := by
            rw [Nat.sub_add_cancel (by omega)]; exact h ▸ hq0
          exact hs.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hsq).mp h1))
        have hsd : s ∣ Nat.card PSL(2, F) := by
          have h1 := card_psl_aux F (by rw [Nat.card_eq_fintype_card]; exact Nat.odd_iff.mpr hodd)
          have h2' : s ∣ Nat.card PSL(2, F) * 2 := by
            rw [h1, Nat.card_eq_fintype_card]
            refine Dvd.dvd.mul_left (hsq.trans ?_) _
            obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 := ⟨N * 2, by omega⟩
            rw [hm]
            exact ⟨m + 2, by simp only [Nat.add_sub_cancel]; rw [Nat.sub_eq_of_eq_add]; ring⟩
          rcases (Nat.Prime.dvd_mul hs).mp h2' with h | h
          · exact h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h) hs2
        exact ⟨s, 2, hs, hsπ, Nat.prime_two, h2, bad_of_ne_char hs hs2 hsc hsd⟩
      · exact ⟨p, s, hp, hpπ, hs, hsπ, bad_of_char hp hpc d hdd hds⟩
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.mpr hq
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hr
      refine ⟨p, 2, hp, hpπ, Nat.prime_two, h2, bad_of_char hp hpc (Units.mk0 r hr0) ?_ (k := 1) ?_⟩
      · intro h
        have := congrArg Units.val h
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
        rw [sq, ← hr] at this
        exact Ring.neg_one_ne_one_of_char_ne_two hc2 this
      · apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        have hr2 : r ^ 2 = -1 := by rw [sq, ← hr]
        rw [pow_one, hr2]; norm_num
  · exact ⟨p, 2, hp, hpπ, Nat.prime_two, h2, bad_of_ne_char hp hp2 hpc hpd⟩

/-- `|PSL(2, q)| = q(q² - 1)/2` for `q` odd. -/
theorem card_psl_two_mul_two (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    Nat.card PSL(2, F) * 2 = Nat.card F * (Nat.card F ^ 2 - 1) :=
  card_psl_aux F hF

end CFSGOutside.Arad
