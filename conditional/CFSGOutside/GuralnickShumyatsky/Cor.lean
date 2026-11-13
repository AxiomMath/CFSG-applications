import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime
import CFSGOutside.GuralnickShumyatsky.Main

/-!
# Guralnick–Shumyatsky, Corollary 3.4: `G' = ⟨C_G(a)' | a ∈ A#⟩`
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

theorem CopAct.isPGroup {X : Type*} [Group X] {q : ℕ} {G A : Subgroup X} (hA : CopAct q G A) :
    IsPGroup q A := by
  haveI := Fact.mk hA.prime
  intro a
  exact ⟨1, by rw [pow_one]; exact Subtype.ext (hA.exp a a.2)⟩

/-- **Guralnick–Shumyatsky, Corollary 3.4.** If `A` is elementary abelian of order `q³` and acts
coprimely on the finite group `G`, then `G' = ⟨C_G(a)' | a ∈ A#⟩`. -/
theorem corollary_3_4 [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q : ℕ} {G A : Subgroup X}
    (hA : CopAct q G A) (hA3 : Nat.card A = q ^ 3) :
    ⁅G, G⁆ = ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen G a, cen G a⁆ := by
  set H : Subgroup X := ⨆ (a : X) (_ : a ∈ A) (_ : a ≠ 1), ⁅cen G a, cen G a⁆
  set D : Subgroup X := ⁅G, G⁆
  have hHD : H ≤ D :=
    iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => commutator_mono inf_le_left inf_le_left
  refine le_antisymm ?_ hHD
  have hDG : D ≤ G := commutator_self_le G
  -- every Sylow subgroup of `D` can be taken inside `H`
  have hdvd : Nat.card D ∣ Nat.card H := by
    have hD0 : Nat.card D ≠ 0 := Nat.card_pos.ne'
    have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
    refine (Nat.factorization_prime_le_iff_dvd hD0 hH0).mp fun p hp => ?_
    haveI := Fact.mk hp
    obtain ⟨P, hP, hAP⟩ := CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.exists_isSylowOf_normalized_of_coprime
      hA.prime hp hA.isPGroup hA.norm
      hA.coprime
    have hS : IsSylowOf p (P ⊓ D) D :=
      hP.inf_of_le_normalizer hDG (le_normalizer_commutator' le_normalizer le_normalizer)
    have hPH : P ⊓ D ≤ H := by
      rw [show P ⊓ D = gens P G A from theorem_3_1 hA hA3 hP hAP]
      exact iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => inf_le_right
    obtain ⟨Q, hQ⟩ := hS
    have hcard : Nat.card (P ⊓ D : Subgroup X) = p ^ (Nat.card D).factorization p := by
      rw [← hQ, card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity]
    rw [← hp.pow_dvd_iff_le_factorization hH0, ← hcard]
    exact card_dvd_of_le hPH
  exact (eq_of_le_of_card_ge hHD (Nat.le_of_dvd Nat.card_pos hdvd)).ge

/-- **Guralnick–Shumyatsky, Corollary 3.3.** Under the same hypotheses,
`π(G') = ⋃_{a ∈ A#} π(C_G(a)')`. -/
theorem corollary_3_3 [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q : ℕ} {G A : Subgroup X}
    (hA : CopAct q G A) (hA3 : Nat.card A = q ^ 3) (p : ℕ) (hp : p.Prime) :
    p ∣ Nat.card (⁅G, G⁆ : Subgroup X) ↔
      ∃ a ∈ A, a ≠ 1 ∧ p ∣ Nat.card (⁅cen G a, cen G a⁆ : Subgroup X) := by
  haveI := Fact.mk hp
  constructor
  · intro hpD
    obtain ⟨P, hP, hAP⟩ := CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.exists_isSylowOf_normalized_of_coprime
      hA.prime hp hA.isPGroup hA.norm
      hA.coprime
    have hDG : ⁅G, G⁆ ≤ G := commutator_self_le G
    obtain ⟨Q, hQ⟩ := hP.inf_of_le_normalizer hDG
      (le_normalizer_commutator' le_normalizer le_normalizer)
    have hcard : Nat.card (P ⊓ ⁅G, G⁆ : Subgroup X) = p ^ (Nat.card (⁅G, G⁆ : Subgroup X)).factorization p := by
      rw [← hQ, card_map_of_injective (⁅G, G⁆ : Subgroup X).subtype_injective,
        Sylow.card_eq_multiplicity]
    have hne : P ⊓ ⁅G, G⁆ ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hcard
      have h1 : 1 ≤ (Nat.card (⁅G, G⁆ : Subgroup X)).factorization p :=
        (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hpD
      have := Nat.one_lt_pow (by omega) hp.one_lt (n := (Nat.card (⁅G, G⁆ : Subgroup X)).factorization p)
      omega
    rw [theorem_3_1 hA hA3 hP hAP] at hne
    by_contra hc
    push Not at hc
    apply hne
    refine eq_bot_iff.mpr (iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_)
    -- `P ∩ C_G(a)'` is a `p`-subgroup of a `p'`-group
    have hpg : IsPGroup p (P ⊓ ⁅cen G a, cen G a⁆ : Subgroup X) :=
      hP.isPGroup.to_le inf_le_left
    have hdvd := card_dvd_of_le (inf_le_right : P ⊓ ⁅cen G a, cen G a⁆ ≤ ⁅cen G a, cen G a⁆)
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero, card_eq_one] at hk; exact hk.le
    · exact absurd ((dvd_pow_self p k.succ_ne_zero).trans (hk ▸ hdvd)) (hc a ha ha1)
  · rintro ⟨a, _, _, hpa⟩
    exact hpa.trans (card_dvd_of_le (commutator_mono inf_le_left inf_le_left))

end CFSGOutside.GuralnickShumyatsky

