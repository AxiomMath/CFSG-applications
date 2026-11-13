import CFSGOutside.HallPaige.Transport
import CFSGOutside.HallPaige.CatalogueDefs
import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Dispatching the simple case along the classification

`CatalogueCase i` is the minimal-counterexample step for the catalogue group `i.Group`. Given the
classification statement, the catalogue cases give the simple case for every finite simple group.
The cyclic case is proved here.
-/

namespace CFSGOutside.HallPaige

open TauCeti

universe u

/-- The simple case for every finite simple group, from the classification and the catalogue
cases. -/
theorem simple_case_of_catalogue (hCFSG : ClassificationStatement.{0})
    (hcat : ∀ i, CatalogueCase i) (G : Type u) [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hG : IsGood G) (hP : ProperSubgroupsAdmissible G) : HasCompleteMapping G := by
  obtain ⟨i, ⟨e⟩⟩ := classificationStatement_of_zero.{u} hCFSG G
  exact HasCompleteMapping.of_mulEquiv e.symm
    (hcat i (IsGood.of_mulEquiv e hG) (ProperSubgroupsAdmissible.of_mulEquiv e hP))

/-- A finite group of order `2` is not good. -/
theorem not_isGood_of_card_eq_two {G : Type*} [Group G] [Finite G] (h : Nat.card G = 2) :
    ¬ IsGood G := by
  intro hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  have hcard : Nat.card (P : Subgroup G) = 2 := by
    rw [P.card_eq_multiplicity, h, Nat.prime_two.factorization_self, pow_one]
  rcases hG P with hb | hc
  · rw [hb, Subgroup.card_bot] at hcard
    omega
  · exact hc (isCyclic_of_prime_card (p := 2) hcard)

/-- The cyclic entries of the list. -/
theorem catalogueCase_cyclic (p : ℕ) (hp : p.Prime) : CatalogueCase (.cyclic p hp) := by
  intro hG _
  have : Fact p.Prime := ⟨hp⟩
  change HasCompleteMapping (Multiplicative (ZMod p))
  change IsGood (Multiplicative (ZMod p)) at hG
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    exact Nat.card_zmod p
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact absurd hG (not_isGood_of_card_eq_two hcard)
  · exact hasCompleteMapping_of_odd (by rw [hcard]; exact hodd)

end CFSGOutside.HallPaige
