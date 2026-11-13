import CFSGOutside.GuralnickShumyatsky.Simple
import CFSGOutside.GuralnickShumyatsky.Step
import CFSGOutside.GuralnickShumyatsky.Abelian

/-!
# Guralnick–Shumyatsky, Theorem 3.1 (= Theorem 1.4)

Let `A` be an elementary abelian `q`-group of order `q³` acting coprimely on a finite group `G`,
and let `P` be an `A`-invariant Sylow `p`-subgroup of `G`. Then
`P ∩ G' = ⟨P ∩ C_G(a)' | a ∈ A#⟩`.

We work inside a finite group `X` containing `G` and `A` as subgroups, with `A` normalizing `G`.
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup
open scoped commutatorElement

/-- The induction step of Theorem 3.1, when `X = G A`. -/
theorem main_top [CFSGOutside.Corpus.Proposition116B.{0, 0}] [CFSGOutside.Corpus.CfsgClassification]
    [CFSGOutside.Corpus.I713PPrimeHolds] [CFSGOutside.Corpus.OddOrder.{0}]
    [CFSGOutside.Corpus.Gaschutz.{0}] [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    {Y : Type} [Group Y] [Finite Y] {q p : ℕ} [Fact p.Prime] {G A P : Subgroup Y}
    (hA : CopAct q G A) (hA3 : q ^ 3 ≤ Nat.card A) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set Y)) (hGA : G ⊔ A = ⊤)
    (IH : ∀ (Z : Type) [Group Z] [Finite Z] (G' A' P' : Subgroup Z), Nat.card G' < Nat.card G →
      CopAct q G' A' → q ^ 3 ≤ Nat.card A' → IsSylowOf p P' G' →
      A' ≤ normalizer (P' : Set Z) → P' ⊓ ⁅G', G'⁆ ≤ gens P' G' A') :
    P ⊓ ⁅G, G⁆ ≤ gens P G A := by
  haveI hGn : G.Normal := G_normal hA hGA
  have hAn : ∀ (H : Subgroup Y) [H.Normal], A ≤ normalizer (H : Set Y) := fun H _ =>
    le_normalizer_of_normal' H A
  -- induction hypothesis applied to a proper normal subgroup
  have sub : ∀ H : Subgroup Y, H.Normal → H ≤ G → H ≠ G → P ⊓ H ⊓ ⁅H, H⁆ ≤ gens P G A := by
    intro H hH hHG hne
    have hlt : Nat.card H < Nat.card G :=
      lt_of_le_of_ne (card_le_of_le hHG) fun h => hne (eq_of_le_of_card_ge hHG h.ge)
    exact (IH Y H A (P ⊓ H) hlt (hA.mono hHG (hAn H)) hA3
      (hP.inf_of_le_normalizer hHG (le_normalizer_of_normal' H G))
      (le_normalizer_inf' hAP (hAn H))).trans (gens_mono A inf_le_left hHG)
  -- induction hypothesis applied to a quotient
  have step : ∀ N : Subgroup Y, N.Normal → N ≤ G → N ≠ ⊥ →
      P ⊓ ⁅G, G⁆ ≤ gens P G A ⊔ (P ⊓ N) := by
    intro N hN hNG hN1
    exact quot_step_normal hA hP hAP hNG
      (IH (Y ⧸ N) (G.map (QuotientGroup.mk' N)) (A.map (QuotientGroup.mk' N))
        (P.map (QuotientGroup.mk' N)) (card_map_mk_lt hNG hN1) hA.quot
        (by rwa [card_map_mk_of_coprime hA hNG]) (isSylowOf_map hP _)
        ((map_mono hAP).trans (le_normalizer_map _)))
  by_cases h1 : ⁅G, G⁆ = ⊥
  · rw [h1, inf_bot_eq]; exact bot_le
  have hDG : ⁅G, G⁆ ≤ G := commutator_self_le G
  by_cases hperf : ⁅G, G⁆ = G
  swap
  · -- `G` is not perfect
    by_cases h2 : ⁅⁅G, G⁆, ⁅G, G⁆⁆ = ⊥
    · -- `G'` is abelian: Lemma 2.3 with `N = G`
      have hcomm : ∀ x ∈ ⁅G, G⁆, ∀ y ∈ ⁅G, G⁆, x * y = y * x := by
        intro x hx y hy
        have : ⁅x, y⁆ ∈ ⁅⁅G, G⁆, ⁅G, G⁆⁆ := commutator_mem_commutator hx hy
        rw [h2, mem_bot] at this
        exact (commutatorElement_eq_one_iff_mul_comm).mp this
      have h23 := commutator_eq_iSup hA hA3 (N := G) le_rfl (le_normalizer_of_normal' G G)
        hA.norm
      have hS : IsSylowOf p (P ⊓ ⁅G, G⁆) ⁅G, G⁆ :=
        hP.inf_of_le_normalizer hDG (le_normalizer_of_normal' _ G)
      refine (isSylowOf_le_iSup_inf hcomm hS
        (fun a => ⨆ (_ : a ∈ A) (_ : a ≠ 1), ⁅cen G a, cen G a⁆) ?_ h23.le).trans ?_
      · intro a
        exact iSup_le fun _ => iSup_le fun _ =>
          commutator_mono inf_le_left inf_le_left
      · refine iSup_le fun a => ?_
        by_cases ha : a ∈ A
        · by_cases ha1 : a ≠ 1
          · rw [iSup_pos ha, iSup_pos ha1]
            exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1
              (inf_le_inf_right _ inf_le_left)))
          · rw [iSup_pos ha, iSup_neg ha1, inf_bot_eq]; exact bot_le
        · rw [iSup_neg ha, inf_bot_eq]; exact bot_le
    · -- `G'' ≠ 1`: quotient by `G''`
      have hD : ⁅G, G⁆ ≠ G := hperf
      refine (step _ inferInstance ((commutator_self_le _).trans hDG) h2).trans
        (sup_le le_rfl ?_)
      refine le_trans ?_ (sub _ inferInstance hDG hD)
      exact le_inf (inf_le_inf_left _ (commutator_self_le _)) inf_le_right
  -- `G` is perfect
  have hG1 : G ≠ ⊥ := fun h => h1 (by rw [h, commutator_bot_left])
  have hPG : P ≤ G := hP.le
  have hPD : P ⊓ ⁅G, G⁆ = P := by rw [hperf]; exact inf_eq_left.mpr hPG
  rw [hPD]
  have step' : ∀ N : Subgroup Y, N.Normal → N ≤ G → N ≠ ⊥ → P ≤ gens P G A ⊔ (P ⊓ N) :=
    fun N hN hNG hN1 => by have := step N hN hNG hN1; rwa [hPD] at this
  -- a minimal normal subgroup `N` of `X = GA` inside `G`
  obtain ⟨N, ⟨hNn, hNG, hN1⟩, hNmin⟩ :=
    (measure fun H : Subgroup Y => Nat.card H).wf.has_min
      {N : Subgroup Y | N.Normal ∧ N ≤ G ∧ N ≠ ⊥} ⟨G, hGn, le_rfl, hG1⟩
  haveI := hNn
  have hmin : ∀ M : Subgroup Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hMN
    by_contra hc
    push Not at hc
    refine hNmin M ⟨hM, hMN.trans hNG, hc.1⟩ ?_
    exact lt_of_le_of_ne (card_le_of_le hMN) fun h => hc.2 (eq_of_le_of_card_ge hMN h.ge)
  by_cases hNG' : N = G
  · subst hNG'
    refine le_gens_of_minimal hA hA3 hP hAP hG1 hperf fun M hMG hGM hAM => ?_
    exact hmin M (normal_of_le_normalizer hGA hGM hAM) hMG
  by_cases hNperf : ⁅N, N⁆ = N
  · refine (step' N hNn hNG hN1).trans (sup_le le_rfl ?_)
    have := sub N hNn hNG hNG'
    rwa [hNperf, inf_assoc, inf_idem] at this
  have hNab : ⁅N, N⁆ = ⊥ := (hmin _ inferInstance (commutator_self_le N)).resolve_right hNperf
  have hcommN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    have : ⁅x, y⁆ ∈ ⁅N, N⁆ := commutator_mem_commutator hx hy
    rw [hNab, mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm).mp this
  by_cases hPN : P ⊓ N = ⊥
  · have := step' N hNn hNG hN1
    rwa [hPN, sup_bot_eq] at this
  have hS : IsSylowOf p (P ⊓ N) N := hP.inf_of_le_normalizer hNG (le_normalizer_of_normal' N G)
  haveI := isSylowOf_normal_of_comm hcommN hS
  have hNP : N ≤ P := by
    have := (hmin _ inferInstance inf_le_right).resolve_left hPN
    rw [← this]; exact inf_le_left
  have hPgN : P ≤ gens P G A ⊔ N :=
    (step' N hNn hNG hN1).trans (sup_le le_sup_left (inf_le_right.trans le_sup_right))
  by_cases hNG2 : ⁅N, G⁆ = ⊥
  · -- `N` is central: Gaschütz and the Frattini argument
    refine central_case hP hperf hNP hNG2 hN1 (gens_le P G A) hPgN ?_
    have hMn : (N ⊓ (frattini P).map P.subtype).Normal :=
      normal_of_le_normalizer hGA (le_normalizer_of_le_of_commutator_eq_bot inf_le_left hNG2)
        (le_normalizer_inf' (hAn N) (le_normalizer_frattini hAP))
    rcases hmin _ hMn inf_le_left with h | h
    · exact Or.inl h
    · right; rw [← h]; exact inf_le_right
  · -- `[N, G] = N`: Lemma 2.3
    have hNG3 : ⁅N, G⁆ = N :=
      (hmin _ inferInstance (commutator_le_left N G)).resolve_left hNG2
    have hNgens : N ≤ gens P G A := by
      rw [← hNG3, commutator_eq_iSup hA hA3 hNG (le_normalizer_of_normal' N G) (hAn N)]
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      refine le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 (le_inf ?_ ?_)))
      · exact (commutator_mono inf_le_left inf_le_left).trans (hNG3.le.trans hNP)
      · exact commutator_mono (inf_le_inf_right _ hNG) le_rfl
    exact hPgN.trans (sup_le le_rfl hNgens)

/-- Theorem 3.1, inequality form, for `|A| ≥ q³`. -/
theorem le_gens_aux [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    (q p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (Y : Type) [Group Y] [Finite Y] (G A P : Subgroup Y), Nat.card G = n → CopAct q G A →
      q ^ 3 ≤ Nat.card A → IsSylowOf p P G → A ≤ normalizer (P : Set Y) →
      P ⊓ ⁅G, G⁆ ≤ gens P G A := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro Y _ _ G A P hn hA hA3 hP hAP
    set K := G ⊔ A
    have hGK : G ≤ K := le_sup_left
    have hAK : A ≤ K := le_sup_right
    have hPK : P ≤ K := hP.le.trans hGK
    have hinj : Function.Injective K.subtype := K.subtype_injective
    have hG : (G.subgroupOf K).map K.subtype = G := map_subgroupOf_eq_of_le hGK
    have hAm : (A.subgroupOf K).map K.subtype = A := map_subgroupOf_eq_of_le hAK
    refine le_gens_of_subgroupOf hGK hAK hPK ?_
    refine main_top (hA.subgroupOf hGK hAK) (by rwa [card_subgroupOf_of_le hAK])
      (isSylowOf_subgroupOf hP hGK) (le_normalizer_subgroupOf hAP hPK) ?_ ?_
    · apply map_injective hinj
      rw [Subgroup.map_sup, hG, hAm, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · intro Z _ _ G' A' P' hlt
      rw [card_subgroupOf_of_le hGK, hn] at hlt
      exact IH _ hlt Z G' A' P' rfl

/-- **Derived subgroups of fixed points.** Let A be an elementary abelian group of order q³, q prime, acting coprimely
on a finite group G, and write C_G(a)′ for the derived subgroup of the centralizer of a. For every prime p and every
A-invariant Sylow p-subgroup P of G, P ∩ G′ is generated by the subgroups P ∩ C_G(a)′ with a ≠ 1. Consequently G′ is
generated by the C_G(a)′ with a ≠ 1, a prime divides |G′| exactly when it divides some |C_G(a)′|, |G′| ≤
m^(2(q²+q+1)) when every |C_G(a)′| ≤ m, and G′ is generated by m(q²+q+1) elements when every C_G(a)′ is generated by
m.

Source: R. M. Guralnick and P. Shumyatsky, Derived subgroups of fixed points, Israel J. Math. 126 (2001), 345–362,
Theorems 3.1 and 3.6, Corollaries 3.3–3.5. https://doi.org/10.1007/BF02784161

This version takes the corpus theorems it uses as instance arguments; the version in `unconditional/` supplies them
from the CFSG corpus. -/
theorem theorem_3_1 [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.Gaschutz.{0}]
    [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [CFSGOutside.Corpus.ExistsIsSylowOfNormalizedGeOfCoprime.{0}]
    [CFSGOutside.Corpus.ExistsConjEqOfIsSylowOfNormalizedOfCoprime.{0}]
    {X : Type} [Group X] [Finite X] {q p : ℕ} [Fact p.Prime]
    {G A P : Subgroup X} (hA : CopAct q G A) (hA3 : Nat.card A = q ^ 3) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set X)) :
    P ⊓ ⁅G, G⁆ = gens P G A := by
  refine le_antisymm (le_gens_aux q p _ X G A P rfl hA hA3.ge hP hAP) ?_
  refine iSup_le fun a => iSup_le fun _ => iSup_le fun _ => ?_
  exact inf_le_inf_left _ (commutator_mono inf_le_left inf_le_left)

end CFSGOutside.GuralnickShumyatsky

