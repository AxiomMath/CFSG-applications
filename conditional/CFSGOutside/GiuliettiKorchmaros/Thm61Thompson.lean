import CFSGOutside.GiuliettiKorchmaros.Thm61TwoBasic

/-!
# Theorem 6.1: an index-2 subgroup from Thompson's transfer lemma

If `G` has a central involution `z` and a nonabelian Sylow 2-subgroup `S` with a cyclic subgroup `⟨a⟩` of index 2 and
an involution `b ∉ ⟨a⟩`, then `b` is not conjugate into `⟨a⟩` (whose only involution is `z`), so Thompson's transfer
lemma gives a subgroup of index 2.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus

variable {G : Type} [Group G] [Finite G]

theorem exists_index_two_of_involution [ThompsonTransferLemma.{0}] (S : Sylow 2 G) {z : G}
    (hz : z ∈ Subgroup.center G) (hz2 : orderOf z = 2)
    (a b : (S : Subgroup G)) (hidx : (Subgroup.zpowers a).index = 2) (hb : b ∉ Subgroup.zpowers a)
    (hb2 : b ^ 2 = 1) (hnab : ∃ x y : (S : Subgroup G), x * y ≠ y * x) :
    ∃ M : Subgroup G, M.index = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : z ∈ (S : Subgroup G) := mem_sylow_of_central hz hz2 S
  set zS : (S : Subgroup G) := ⟨z, hzS⟩
  have hzS_center : zS ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz y)
  have hzA : zS ∈ Subgroup.zpowers a :=
    TwoGroups.center_le_of_index_two (Subgroup.isCyclic_zpowers a) hidx hnab hzS_center
  set Q : Subgroup G := (Subgroup.zpowers a).map (S : Subgroup G).subtype
  have hQS : Q ≤ (S : Subgroup G) := Subgroup.map_subtype_le _
  have hQidx : Q.relIndex (S : Subgroup G) = 2 := by
    rw [Subgroup.relIndex, show Q.subgroupOf (S : Subgroup G) = Subgroup.zpowers a from
      Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective _]
    exact hidx
  have hQcyc : IsCyclic Q := by
    exact isCyclic_of_surjective ((S : Subgroup G).subtype.subgroupMap (Subgroup.zpowers a))
      (MonoidHom.subgroupMap_surjective _ _)
  have hb1 : (b : G) ≠ 1 := fun h => hb (by rw [show b = 1 from Subtype.ext h]; exact one_mem _)
  have hbo : orderOf (b : G) = 2 := by
    apply orderOf_eq_prime _ hb1
    simpa using congrArg Subtype.val hb2
  have hzQ : z ∈ Q := ⟨zS, hzA, rfl⟩
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  have hQu : ∀ x : G, x⁻¹ * (b : G) * x ∉ Q := by
    intro x hx
    have hsq : (x⁻¹ * (b : G) * x) ^ 2 = 1 := by
      rw [show x⁻¹ * (b : G) * x = x⁻¹ * (b : G) * x⁻¹⁻¹ by rw [inv_inv], conj_pow]
      simp [show (b : G) ^ 2 = 1 by simpa using congrArg Subtype.val hb2]
    have hne : x⁻¹ * (b : G) * x ≠ 1 := fun h => hb1 (by
      calc (b : G) = x * (x⁻¹ * (b : G) * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group)
    have heq := cyclic_involution_unique hQcyc hx hzQ hsq
      (by rw [← hz2]; exact pow_orderOf_eq_one z) hne hz1
    have hbz : (b : G) = z := by
      calc (b : G) = x * (x⁻¹ * (b : G) * x) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [heq]
        _ = z := by rw [Subgroup.mem_center_iff.mp hz x]; group
    exact hb (by rw [show b = zS from Subtype.ext hbz]; exact hzA)
  exact exists_index_two_of_not_mem_pResidual
    (ThompsonTransferLemma.thompson_transfer_lemma S hQS hQidx hbo hQu)

end CFSGOutside.GiuliettiKorchmaros
