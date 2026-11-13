import Mathlib
import CFSGOutside.Corpus.CfsgClassification
import CFSGOutside.Corpus.LieOrderBridgeHolds
import CFSGOutside.Corpus.SporadicOrdersTableHolds

namespace CFSGOutside.OrderShape

open CFSGOutside.Corpus CFSGOutside.Corpus.Open
  CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator
  CFSGOutside.Corpus.HardMathSupport.Solomon.Coordinator.I1420

theorem card_alternating (n : ℕ) (hn : 5 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

/-- A nonabelian finite simple group is sporadic, alternating, or of Lie type, with the exact order. -/
theorem card_shape [CfsgClassification] [LieOrderBridgeHolds] [SporadicOrdersTableHolds]
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    (∃ s : TauCeti.SporadicName, Nat.card G = sporOrd s) ∨
    (∃ n, 5 ≤ n ∧ Nat.card G = n.factorial / 2) ∨
    ∃ idx : TauCeti.ValidLieTypeIndex, Nat.card G = lieOrderFormula idx.1 := by
  obtain ⟨i, ⟨e⟩⟩ := CfsgClassification.cfsg_classification G
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    right; left
    exact ⟨n, hn, (Nat.card_congr e.toEquiv).trans (card_alternating n hn)⟩
  | lie idx =>
    right; right
    exact ⟨idx, LieOrderBridgeHolds.lieOrderBridge_holds idx G ⟨e⟩⟩
  | sporadic s =>
    left
    exact ⟨s, (Nat.card_congr e.toEquiv).trans (SporadicOrdersTableHolds.sporadicOrdersTable_holds s)⟩

/-- Every sporadic order is divisible by 2, 3, 5 and by 7 or 11. -/
theorem sporadic_four_primes (s : TauCeti.SporadicName) :
    2 ∣ sporOrd s ∧ 3 ∣ sporOrd s ∧ 5 ∣ sporOrd s ∧ (7 ∣ sporOrd s ∨ 11 ∣ sporOrd s ∨ 17 ∣ sporOrd s ∨ 19 ∣ sporOrd s) := by
  cases s <;> simp only [sporOrd, orderJ3, orderRu, orderON, orderHN, orderFi23, orderCo1, orderLy,
    orderTh, orderJ4, orderFi24Prime, orderBabyMonster, orderMonster] <;> decide +kernel

theorem sporOrd_pos (s : TauCeti.SporadicName) : 0 < sporOrd s := by
  cases s <;> simp only [sporOrd, orderJ3, orderRu, orderON, orderHN, orderFi23, orderCo1, orderLy,
    orderTh, orderJ4, orderFi24Prime, orderBabyMonster, orderMonster] <;> decide +kernel

end CFSGOutside.OrderShape
