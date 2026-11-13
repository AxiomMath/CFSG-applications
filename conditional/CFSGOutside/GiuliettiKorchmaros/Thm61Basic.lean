import CFSGOutside.GiuliettiKorchmaros.Simple
import CFSGOutside.GiuliettiKorchmaros.Complement
import CFSGOutside.Corpus.Defs.OddCore
import CFSGOutside.Corpus.PPrimeCore

/-!
# Theorem 6.1: basic facts on odd core-free groups

Minimal normal subgroups, the odd core, and inheritance of the hypotheses by subgroups.
-/

namespace CFSGOutside.GiuliettiKorchmaros

open CFSGOutside.Corpus

variable {G : Type} [Group G] [Finite G]

/-- A nontrivial finite group has a minimal normal subgroup. -/
theorem exists_isMinimalNormal (hG : Nontrivial G) : ∃ N : Subgroup G, IsMinimalNormal N := by
  classical
  have hex : ∃ n, ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ Nat.card N = n :=
    ⟨_, ⊤, inferInstance, top_ne_bot, rfl⟩
  obtain ⟨N, hNn, hN1, hNc⟩ := Nat.find_spec hex
  refine ⟨N, hNn, hN1, fun M hM hMN => ?_⟩
  by_cases hM1 : M = ⊥
  · exact Or.inl hM1
  · right
    have hle : Nat.find hex ≤ Nat.card M := Nat.find_min' hex ⟨M, hM, hM1, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hMN (by omega)

/-- In an odd core-free group the odd core is trivial. -/
theorem oddCore_eq_bot (hO : OddCoreFree G) : oddCore G = ⊥ := by
  apply le_antisymm _ bot_le
  -- the odd core is a normal subgroup of odd order
  have hdir : ∀ N ∈ {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}, N = ⊥ := fun N hN => hO N hN.1 hN.2
  rw [oddCore, sSup_le_iff]
  intro N hN
  rw [hdir N hN]

/-- The quotient by the trivial subgroup. -/
noncomputable def quotientBotEquiv (H : Subgroup G) [H.Normal] (hH : H = ⊥) : G ⧸ H ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq hH).trans (QuotientGroup.quotientBot)

/-- The hypothesis `CyclicIndexTwo` passes to subgroups. -/
theorem cyclicIndexTwo_subgroup (hP : CyclicIndexTwo G) (M : Subgroup G) : CyclicIndexTwo M := by
  intro P hP2
  obtain ⟨C, hCP, hC, hidx⟩ := hP (P.map M.subtype) (hP2.map M.subtype)
  have hCM : C ≤ M := hCP.trans (Subgroup.map_subtype_le P)
  refine ⟨C.comap M.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hCP hx)
    rwa [← Subtype.ext hyx]
  · have e : C.comap M.subtype ≃* C :=
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr (by
          rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hCM]))
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · have h1 : (C.comap M.subtype).relIndex P = C.relIndex (P.map M.subtype) := by
      rw [← Subgroup.relIndex_comap]
    rw [h1]; exact hidx

/-- The hypothesis `CyclicIndexTwo` transfers along isomorphisms. -/
theorem cyclicIndexTwo_of_mulEquiv {H : Type} [Group H] (e : G ≃* H) (hP : CyclicIndexTwo G) :
    CyclicIndexTwo H := by
  intro P hP2
  obtain ⟨C, hCP, hC, hidx⟩ := hP (P.map e.symm.toMonoidHom) (hP2.map _)
  refine ⟨C.map e.toMonoidHom, ?_, isCyclic_of_surjective (e.toMonoidHom.subgroupMap C)
    (e.toMonoidHom.subgroupMap_surjective C), ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 (hCP hy)
    simpa using hw
  · have hP' : P = (P.map e.symm.toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map]; ext x; simp
    rw [hP', Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx

/-- The hypothesis `OddCoreFree` transfers along isomorphisms. -/
theorem oddCoreFree_of_mulEquiv {H : Type} [Group H] (e : G ≃* H) (hO : OddCoreFree G) :
    OddCoreFree H := by
  intro M hM hodd
  have hMn : (M.map e.symm.toMonoidHom).Normal := hM.map _ e.symm.surjective
  have hc : Nat.card (M.map e.symm.toMonoidHom) = Nat.card M :=
    Subgroup.card_map_of_injective e.symm.injective
  have h1 := hO _ hMn (by rw [hc]; exact hodd)
  have h2 : M = (M.map e.symm.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map]; ext x; simp
  rw [h2, h1, Subgroup.map_bot]

/-- A subgroup of the center is normal. -/
theorem normal_of_le_center {H : Subgroup G} (h : H ≤ Subgroup.center G) : H.Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (h hn) g, mul_inv_cancel_right]; exact hn⟩

/-- A central element of order 2 lies in every Sylow 2-subgroup. -/
theorem mem_sylow_of_central {z : G} (hz : z ∈ Subgroup.center G) (hz2 : orderOf z = 2)
    (S : Sylow 2 G) : z ∈ (S : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc : Subgroup.zpowers z ≤ Subgroup.center G :=
    (Subgroup.zpowers_le (H := Subgroup.center G)).2 hz
  haveI := normal_of_le_center hzc
  have hp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hzS : (Subgroup.zpowers z ⊔ (S : Subgroup G) : Subgroup G) = S :=
    S.3 (IsPGroup.to_sup_of_normal_left hp S.2) le_sup_right
  rw [← hzS]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

end CFSGOutside.GiuliettiKorchmaros
