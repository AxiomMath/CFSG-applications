import Mathlib

/-!
# Corpus definition: the p′-core

`CFSGOutside.Corpus.pPrimeCore` is `CFSG.pPrimeCore`, copied verbatim from
`CFSG/ThirdParty/QiuzhenCFSG/FeitThompson/PCore/Defs.lean` (line 40) at AxiomMath/CFSG commit
69cb972f587a3ecc035e092253167ff2e303c962. Its normality and coprimality, `CFSG.pPrimeCore_normal` and
`CFSG.pPrimeCore_coprime_card` (`.../PCore/PPrimeCore.lean`, lines 144 and 157), are short and proved here.
-/

open scoped Pointwise

namespace CFSGOutside.Corpus

/-- The `p'`-core of `G`: the supremum of all normal subgroups of order coprime to `p`. -/
def pPrimeCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)}

variable {p : ℕ} {G : Type*} [Group G]

theorem directedOn_normal_pPrimeSubgroups :
    DirectedOn (· ≤ ·) {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} := by
  intro A hA B hB
  obtain ⟨hA_normal, hA_coprime⟩ := hA
  obtain ⟨hB_normal, hB_coprime⟩ := hB
  refine ⟨A ⊔ B, ⟨Subgroup.sup_normal A B, ?_⟩, le_sup_left, le_sup_right⟩
  have hmul : (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) := by
    simpa using Subgroup.mul_normal A B
  have hcard_sup : Nat.card (↥(A ⊔ B)) = Nat.card ((A : Set G) * (B : Set G) : Set G) := by
    simpa using Nat.card_congr (Set.equivOfEq hmul)
  have hcard_mul :
      Nat.card ((A : Set G) * (B : Set G) : Set G) =
        Nat.card B * Nat.card ((A : Set G).image (↑) : Set (G ⧸ B)) := by
    simpa using Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := B) (t := (A : Set G))
  have hset_image :
      ((A : Set G).image (↑) : Set (G ⧸ B)) = (A.map (QuotientGroup.mk' B) : Set (G ⧸ B)) := by
    simp [Subgroup.coe_map]
  have hcard_image :
      Nat.card ((A : Set G).image (↑) : Set (G ⧸ B)) = Nat.card (A.map (QuotientGroup.mk' B)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcoprime_image : Nat.Coprime p (Nat.card ((A : Set G).image (↑) : Set (G ⧸ B))) := by
    rw [hcard_image]
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd A (QuotientGroup.mk' B)) hA_coprime
  rw [hcard_sup, hcard_mul]
  exact Nat.Coprime.mul_right hB_coprime hcoprime_image

theorem mem_pPrimeCore_iff {x : G} :
    x ∈ pPrimeCore p G ↔ ∃ K : Subgroup G, (K.Normal ∧ Nat.Coprime p (Nat.card K)) ∧ x ∈ K := by
  have hne : {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)}.Nonempty :=
    ⟨⊥, inferInstance, by simp⟩
  exact Subgroup.mem_sSup_of_directedOn hne directedOn_normal_pPrimeSubgroups

/-- The `p'`-core is normal. -/
instance pPrimeCore_normal : (pPrimeCore p G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨K, hK, hnK⟩ := mem_pPrimeCore_iff.mp hn
  exact Subgroup.mem_sSup_of_mem hK (hK.1.conj_mem n hnK g)

/-- The order of the `p'`-core is coprime to `p`. -/
theorem pPrimeCore_coprime_card [Finite G] [Fact p.Prime] :
    Nat.Coprime p (Nat.card (pPrimeCore p G)) := by
  have hp : Nat.Prime p := Fact.out
  refine hp.coprime_iff_not_dvd.2 fun hpdvd => ?_
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pPrimeCore p G) p hpdvd
  obtain ⟨K, hK, hxK⟩ := mem_pPrimeCore_iff.mp x.property
  have horder : orderOf (x : G) = p := by simpa [Subgroup.orderOf_coe] using hx
  have hdvd : p ∣ Nat.card K := horder ▸ Subgroup.orderOf_dvd_natCard K hxK
  exact (hp.coprime_iff_not_dvd.1 hK.2) hdvd

end CFSGOutside.Corpus
