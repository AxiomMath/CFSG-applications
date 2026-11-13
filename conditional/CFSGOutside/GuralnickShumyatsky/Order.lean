import CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime
import CFSGOutside.GuralnickShumyatsky.Main
import CFSGOutside.GuralnickShumyatsky.Count

/-!
# Guralnick–Shumyatsky, Theorem 3.6 (= Theorem 1.1): `|G'| ≤ m ^ (2(q² + q + 1))`
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

/-- One step of the induction in `card_commutator_le_prod`. -/
theorem card_commutator_step [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q : ℕ}
    {P A N : Subgroup X} (hA : CopAct q P A) (hA3 : q ^ 3 ≤ Nat.card A)
    (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set X)) (hAN : A ≤ normalizer (N : Set X))
    (IH : Nat.card (⁅⁅N, P⁆, P⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (⁅cenS ⁅N, P⁆ B, cenS P B⁆ : Subgroup X)) :
    Nat.card (⁅N, P⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (⁅cenS N B, cenS P B⁆ : Subgroup X) := by
  set L : Subgroup X := ⁅N, P⁆ with hLdef
  have hLN : L ≤ N := (le_normalizer_iff_commutator_le_left).1 hPN
  have hPL : P ≤ normalizer (L : Set X) :=
    le_normalizer_commutator' hPN (le_normalizer (H := P))
  have hLP : L ≤ P := hLN.trans hNP
  have hWL : ⁅L, P⁆ ≤ L := (le_normalizer_iff_commutator_le_left).1 hPL
  have hWn : L ≤ normalizer ((⁅L, P⁆ : Subgroup X) : Set X) :=
    hLP.trans (le_normalizer_commutator' hPL (le_normalizer (H := P)))
  have hLeq : L = ⨆ B ∈ cycSubs A, ⁅cenS N B, cenS P B⁆ :=
    (commutator_eq_iSup hA hA3 hNP hPN hAN).trans (iSup_eq_iSup_cycSubs N P A)
  have hFL : ∀ B ∈ cycSubs A, (⁅cenS N B, cenS P B⁆ : Subgroup X) ≤ L := by
    intro B hB
    rw [hLeq]
    exact le_iSup₂_of_le B hB le_rfl
  have key := card_mul_prod_le (cycSubs A) (fun B => (⁅cenS N B, cenS P B⁆ : Subgroup X))
    (L := L) (W := ⁅L, P⁆) hWL hWn hFL (hLeq.le.trans le_sup_right) (by
      intro B hB B' hB'
      exact commutator_mono (hFL B hB) ((hFL B' hB').trans hLP))
  have hpos : 0 < ∏ B ∈ cycSubs A, Nat.card ((⁅cenS N B, cenS P B⁆ : Subgroup X) ⊓ ⁅L, P⁆ :
      Subgroup X) := Finset.prod_pos fun _ _ => Nat.card_pos
  have h1 : ∏ B ∈ cycSubs A, Nat.card (⁅cenS L B, cenS P B⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card ((⁅cenS N B, cenS P B⁆ : Subgroup X) ⊓ ⁅L, P⁆ :
        Subgroup X) := by
    refine Finset.prod_le_prod' fun B _ => Subgroup.card_le_of_le (le_inf ?_ ?_)
    · exact commutator_mono (inf_le_inf_right _ hLN) le_rfl
    · exact commutator_mono inf_le_left inf_le_left
  have h2 : Nat.card (⁅L, P⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card ((⁅cenS N B, cenS P B⁆ : Subgroup X) ⊓ ⁅L, P⁆ : Subgroup X) := IH.trans h1
  have h3 : Nat.card L * ∏ B ∈ cycSubs A, Nat.card ((⁅cenS N B, cenS P B⁆ : Subgroup X) ⊓ ⁅L, P⁆ :
      Subgroup X) ≤ (∏ B ∈ cycSubs A, Nat.card (⁅cenS N B, cenS P B⁆ : Subgroup X)) *
      ∏ B ∈ cycSubs A, Nat.card ((⁅cenS N B, cenS P B⁆ : Subgroup X) ⊓ ⁅L, P⁆ :
      Subgroup X) :=
    key.trans (by rw [mul_comm _ (∏ B ∈ cycSubs A, Nat.card (⁅cenS N B, cenS P B⁆ : Subgroup X))]
                  exact Nat.mul_le_mul_left _ h2)
  exact Nat.le_of_mul_le_mul_right h3 hpos

/-- Lemma 2.3 (second part), as an order bound, for a `p`-group `P`: if `N` is an `A`-invariant
normal subgroup of `P` then `|[N, P]| ≤ ∏_{B} |[C_N(B), C_P(B)]|`, the product over the
nontrivial cyclic subgroups `B` of `A`. -/
theorem card_commutator_le_prod [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q p : ℕ} [Fact p.Prime]
    {P A N : Subgroup X} (hA : CopAct q P A) (hA3 : q ^ 3 ≤ Nat.card A) (hPp : IsPGroup p P)
    (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set X)) (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (⁅N, P⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (⁅cenS N B, cenS P B⁆ : Subgroup X) := by
  haveI : Group.IsNilpotent P := hPp.isNilpotent
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries P).1 inferInstance
  have main : ∀ j k : ℕ, c ≤ k + j → ∀ N : Subgroup X, N ≤ P.lowerCentralSeries k →
      N ≤ P → P ≤ normalizer (N : Set X) → A ≤ normalizer (N : Set X) →
      Nat.card (⁅N, P⁆ : Subgroup X) ≤
        ∏ B ∈ cycSubs A, Nat.card (⁅cenS N B, cenS P B⁆ : Subgroup X) := by
    intro j
    induction j with
    | zero =>
      intro k hk N hN _ _ _
      have : P.lowerCentralSeries k = ⊥ := by
        rw [eq_bot_iff, ← hc]
        exact (Subgroup.lowerCentralSeries_antitone P (by omega))
      have hNb : N = ⊥ := le_bot_iff.1 (this ▸ hN)
      subst hNb
      rw [commutator_bot_left, Subgroup.card_bot]
      exact Finset.prod_pos fun _ _ => Nat.card_pos
    | succ j ih =>
      intro k hk N hN hNP hPN hAN
      refine card_commutator_step hA hA3 hNP hPN hAN ?_
      have hLN : (⁅N, P⁆ : Subgroup X) ≤ N := (le_normalizer_iff_commutator_le_left).1 hPN
      refine ih (k + 1) (by omega) _ ?_ (hLN.trans hNP)
        (le_normalizer_commutator' hPN (le_normalizer (H := P)))
        (le_normalizer_commutator' hAN hA.norm)
      rw [Subgroup.lowerCentralSeries_succ]
      exact commutator_mono hN le_rfl
  exact main c 0 (by omega) N (by rw [Subgroup.lowerCentralSeries_zero]; exact hNP) hNP hPN hAN

/-- From Theorem 3.1 and Lemma 2.3: `|P ∩ G'| ≤ ∏_B |P ∩ C_G(B)'|²`. -/
theorem card_inf_commutator_le [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q p : ℕ} [Fact p.Prime]
    {G A P : Subgroup X} (hA : CopAct q G A) (hA3 : Nat.card A = q ^ 3) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set X)) :
    Nat.card (P ⊓ ⁅G, G⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) ^ 2 := by
  have hPG := hP.le
  have hLeq : P ⊓ ⁅G, G⁆ = ⨆ B ∈ cycSubs A, P ⊓ ⁅cenS G B, cenS G B⁆ :=
    (theorem_3_1 hA hA3 hP hAP).trans (gens_eq_iSup_cycSubs P G A)
  set L : Subgroup X := P ⊓ ⁅G, G⁆ with hLdef
  have hLP : L ≤ P := inf_le_left
  have hWL : ⁅P, P⁆ ≤ L := le_inf (commutator_self_le P) (commutator_mono hPG hPG)
  have hWn : L ≤ normalizer ((⁅P, P⁆ : Subgroup X) : Set X) :=
    hLP.trans (le_normalizer_commutator' (le_normalizer (H := P)) (le_normalizer (H := P)))
  have hFL : ∀ B ∈ cycSubs A, (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) ≤ L := by
    intro B hB
    rw [hLeq]
    exact le_iSup₂_of_le B hB le_rfl
  have key := card_mul_prod_le (cycSubs A) (fun B => (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X))
    (L := L) (W := ⁅P, P⁆) hWL hWn hFL (hLeq.le.trans le_sup_right) (by
      intro B hB B' hB'
      exact commutator_mono inf_le_left inf_le_left)
  have hpos : 1 ≤ ∏ B ∈ cycSubs A, Nat.card ((P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) ⊓ ⁅P, P⁆ :
      Subgroup X) := Finset.prod_pos fun _ _ => Nat.card_pos
  have hA' : CopAct q P A := hA.mono hPG hAP
  have hP1 := card_commutator_le_prod hA' (by rw [hA3]) hP.isPGroup (le_refl P)
    (le_normalizer (H := P)) hAP
  have hP2 : ∏ B ∈ cycSubs A, Nat.card (⁅cenS P B, cenS P B⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) := by
    refine Finset.prod_le_prod' fun B _ => Subgroup.card_le_of_le (le_inf ?_ ?_)
    · exact (commutator_self_le _).trans inf_le_left
    · exact commutator_mono (inf_le_inf_right _ hPG) (inf_le_inf_right _ hPG)
  have h1 : Nat.card L ≤ Nat.card L * ∏ B ∈ cycSubs A, Nat.card
      ((P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) ⊓ ⁅P, P⁆ : Subgroup X) :=
    Nat.le_mul_of_pos_right _ hpos
  have h2 := h1.trans key
  have h3 : Nat.card (⁅P, P⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) := hP1.trans hP2
  calc Nat.card L ≤ _ := h2
    _ ≤ (∏ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X)) *
        ∏ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) :=
        Nat.mul_le_mul_right _ h3
    _ = _ := by rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun B _ => (sq _).symm

theorem card_of_isSylowOf {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : IsSylowOf p P K) :
    Nat.card P = p ^ (Nat.card K).factorization p := by
  obtain ⟨Q, rfl⟩ := h
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact Sylow.card_eq_multiplicity Q

/-- **Guralnick–Shumyatsky, Theorem 3.6 (= Theorem 1.1).** Let `A` be an elementary abelian group
of order `q³` acting coprimely on the finite group `G` (here: subgroups of a finite group `X`,
`A` normalizing `G`, `q ∤ |G|`). If `|C_G(a)'| ≤ m` for every `a ∈ A#`, then
`|G'| ≤ m ^ (2(q² + q + 1))`. -/
theorem theorem_3_6 [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q m : ℕ} {G A : Subgroup X}
    (hA : CopAct q G A) (hA3 : Nat.card A = q ^ 3)
    (hm : ∀ a ∈ A, a ≠ 1 → Nat.card (⁅cen G a, cen G a⁆ : Subgroup X) ≤ m) :
    Nat.card (⁅G, G⁆ : Subgroup X) ≤ m ^ (2 * (q ^ 2 + q + 1)) := by
  haveI : Fact q.Prime := ⟨hA.prime⟩
  have hApg : IsPGroup q A := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : g ^ q = 1 := Subtype.ext (hA.exp g.1 g.2)
    rcases (Nat.dvd_prime hA.prime).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have hdvd : Nat.card (⁅G, G⁆ : Subgroup X) ∣
      ∏ B ∈ cycSubs A, Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X) ^ 2 := by
    have hne : ∀ B ∈ cycSubs A, Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X) ^ 2 ≠ 0 :=
      fun B _ => (pow_pos Nat.card_pos 2).ne'
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (Finset.prod_ne_zero_iff.2 hne)]
    intro p
    by_cases hp : p.Prime
    swap
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP, hAP⟩ := CFSGOutside.Corpus.ExistsIsSylowOfNormalizedOfCoprime.exists_isSylowOf_normalized_of_coprime
      (r := p) hA.prime hp hApg
      hA.norm hA.coprime
    have h1 := card_inf_commutator_le hA hA3 hP hAP
    have hK : IsSylowOf p (P ⊓ ⁅G, G⁆) ⁅G, G⁆ :=
      hP.inf_of_le_normalizer (commutator_self_le G)
        (le_normalizer_commutator' (le_normalizer (H := G)) (le_normalizer (H := G)))
    have hC : ∀ B ∈ cycSubs A, Nat.card (P ⊓ ⁅cenS G B, cenS G B⁆ : Subgroup X) =
        p ^ (Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X)).factorization p := by
      intro B hB
      obtain ⟨a, ha, _, rfl⟩ := mem_cycSubs.1 hB
      rw [← cen_eq_cenS]
      exact card_of_isSylowOf (isSylowOf_inf_commutator_cen hA hP hAP ha)
    rw [Finset.prod_congr rfl (fun B hB => by rw [hC B hB]),
      card_of_isSylowOf hK] at h1
    have e1 : ∏ B ∈ cycSubs A, (p ^ (Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X)).factorization p) ^ 2
        = p ^ ∑ B ∈ cycSubs A, 2 * (Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X)).factorization p := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun B _ => (pow_mul' _ _ _).symm
    rw [e1] at h1
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    rw [Nat.factorization_prod hne, Finsupp.finset_sum_apply]
    refine h2.trans (le_of_eq (Finset.sum_congr rfl fun B _ => ?_))
    rw [Nat.factorization_pow]
    simp
  have hle : Nat.card (⁅G, G⁆ : Subgroup X) ≤
      ∏ B ∈ cycSubs A, Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X) ^ 2 :=
    Nat.le_of_dvd (Finset.prod_pos fun _ _ => pow_pos Nat.card_pos 2) hdvd
  have hle2 : ∏ B ∈ cycSubs A, Nat.card (⁅cenS G B, cenS G B⁆ : Subgroup X) ^ 2 ≤
      ∏ B ∈ cycSubs A, m ^ 2 := by
    refine Finset.prod_le_prod' fun B hB => ?_
    obtain ⟨a, ha, ha1, rfl⟩ := mem_cycSubs.1 hB
    rw [← cen_eq_cenS]
    exact Nat.pow_le_pow_left (hm a ha ha1) 2
  refine hle.trans (hle2.trans (le_of_eq ?_))
  rw [Finset.prod_const, card_cycSubs hA hA3, ← pow_mul, mul_comm]

end CFSGOutside.GuralnickShumyatsky

