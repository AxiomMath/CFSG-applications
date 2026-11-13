import CFSGOutside.Corpus.MinimalNormalSimpleFactors
import CFSGOutside.GuralnickShumyatsky.Gen
import CFSGOutside.GuralnickShumyatsky.PerfectFix
import CFSGOutside.GuralnickShumyatsky.SimpleAux
import CFSGOutside.GuralnickShumyatsky.Transport

/-!
# The characteristically simple case (Guralnick–Shumyatsky, Lemma 3.7)
-/

namespace CFSGOutside.GuralnickShumyatsky

open Subgroup

variable {X : Type} [Group X]

/-- Guralnick–Shumyatsky, Lemma 3.7 in the case used in the proof of Theorem 3.1, when moreover
`X = G A`. -/
theorem le_gens_of_minimal_top [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [Finite X] {q p : ℕ} [Fact p.Prime] {G A P : Subgroup X}
    (hA : CopAct q G A) (hA3 : q ^ 3 ≤ Nat.card A) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set X)) (hG1 : G ≠ ⊥) (hperf : ⁅G, G⁆ = G)
    (hmin : ∀ M : Subgroup X, M ≤ G → G ≤ normalizer (M : Set X) → A ≤ normalizer (M : Set X) →
      M = ⊥ ∨ M = G) (hGA : G ⊔ A = ⊤) :
    P ≤ gens P G A := by
  haveI hGn : G.Normal := G_normal hA hGA
  have hq2 := q_ne_two hA hG1 hperf
  have hmin' : ∀ M : Subgroup X, M.Normal → M ≤ G → M = ⊥ ∨ M = G := fun M hM hMG =>
    hmin M hMG (le_normalizer_of_normal) (by
      rw [← normalizer_eq_top_iff] at hM
      rw [hM]; exact le_top)
  obtain ⟨r, S, hr, hSG, hSs, hSc, hSn, e, he⟩ := CFSGOutside.Corpus.MinimalNormalSimpleFactors.minimal_normal_simple_factors
    hGn hG1 hmin'
  exact main_core ⟨r, hr, S, hSG, hSs, hSc, hSn, hG1, hperf, e, he⟩ hA hA3 hP hAP hq2 hGA

/-- Guralnick–Shumyatsky, Lemma 3.7 in the case used in the proof of Theorem 3.1: if `G` is perfect
and has no proper nontrivial `A`-invariant normal subgroups, then
`P = ⟨P ∩ C_G(a)' | a ∈ A#⟩`. -/
theorem le_gens_of_minimal [CFSGOutside.Corpus.Proposition116B.{0, 0}]
    [CFSGOutside.Corpus.CfsgClassification] [CFSGOutside.Corpus.I713PPrimeHolds]
    [CFSGOutside.Corpus.OddOrder.{0}] [CFSGOutside.Corpus.MinimalNormalSimpleFactors.{0}]
    [Finite X] {q p : ℕ} [Fact p.Prime] {G A P : Subgroup X}
    (hA : CopAct q G A) (hA3 : q ^ 3 ≤ Nat.card A) (hP : IsSylowOf p P G)
    (hAP : A ≤ normalizer (P : Set X)) (hG1 : G ≠ ⊥) (hperf : ⁅G, G⁆ = G)
    (hmin : ∀ M : Subgroup X, M ≤ G → G ≤ normalizer (M : Set X) → A ≤ normalizer (M : Set X) →
      M = ⊥ ∨ M = G) :
    P ≤ gens P G A := by
  set K := G ⊔ A
  have hGK : G ≤ K := le_sup_left
  have hAK : A ≤ K := le_sup_right
  have hPK : P ≤ K := hP.le.trans hGK
  have hinj : Function.Injective K.subtype := K.subtype_injective
  have hG : (G.subgroupOf K).map K.subtype = G := map_subgroupOf_eq_of_le hGK
  have hAm : (A.subgroupOf K).map K.subtype = A := map_subgroupOf_eq_of_le hAK
  have hPm : (P.subgroupOf K).map K.subtype = P := map_subgroupOf_eq_of_le hPK
  have key := le_gens_of_minimal_top (G := G.subgroupOf K) (A := A.subgroupOf K)
    (P := P.subgroupOf K) (hA.subgroupOf hGK hAK) (by rwa [card_subgroupOf_of_le hAK])
    (isSylowOf_subgroupOf hP hGK) (le_normalizer_subgroupOf hAP hPK)
    (by
      intro h
      apply hG1
      rw [← hG, h, Subgroup.map_bot])
    (by
      apply map_injective hinj
      rw [map_commutator, hG]; exact hperf)
    (by
      intro M hMG hGM hAM
      have h1 : M.map K.subtype ≤ G := hG ▸ map_mono hMG
      have h2 : G ≤ normalizer ((M.map K.subtype : Subgroup X) : Set X) :=
        hG ▸ (map_mono hGM).trans (le_normalizer_map _)
      have h3 : A ≤ normalizer ((M.map K.subtype : Subgroup X) : Set X) :=
        hAm ▸ (map_mono hAM).trans (le_normalizer_map _)
      rcases hmin _ h1 h2 h3 with h | h
      · left; exact (map_eq_bot_iff_of_injective M hinj).mp h
      · right; apply map_injective hinj; rw [h, hG])
    (by
      apply map_injective hinj
      rw [Subgroup.map_sup, hG, hAm, ← MonoidHom.range_eq_map, Subgroup.range_subtype])
  have := map_mono (f := K.subtype) key
  rwa [map_gens_of_injective _ hinj, hPm, hG, hAm] at this

end CFSGOutside.GuralnickShumyatsky
