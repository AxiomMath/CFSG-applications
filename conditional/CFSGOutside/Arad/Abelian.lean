import CFSGOutside.Arad.Defs

/-!
# Arad, Theorem B(iii), abelian case: abelian Sylow `2`-subgroups pass to subgroups and quotients
-/

namespace CFSGOutside.Arad

/-- The Sylow `2`-subgroups of `G` are abelian. -/
def SylowTwoAbelian (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 2 G, IsMulCommutative (P : Subgroup G)

theorem isMulCommutative_of_injective {K L : Type*} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) (h : IsMulCommutative L) : IsMulCommutative K :=
  ⟨⟨fun a b => hf (by rw [map_mul, map_mul, h.is_comm.comm])⟩⟩

theorem isMulCommutative_of_surjective {K L : Type*} [Group K] [Group L] (f : K →* L)
    (hf : Function.Surjective f) (h : IsMulCommutative K) : IsMulCommutative L := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  rw [← map_mul, ← map_mul, h.is_comm.comm]

theorem sylowTwoAbelian_subgroup {G : Type*} [Group G] [Finite G] (h : SylowTwoAbelian G)
    (H : Subgroup G) : SylowTwoAbelian H := by
  intro Q
  obtain ⟨P, hle⟩ := ((Q.isPGroup').map H.subtype).exists_le_sylow
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : ((a : H) : G) ∈ (P : Subgroup G) := hle ⟨a, a.2, rfl⟩
  have hb : ((b : H) : G) ∈ (P : Subgroup G) := hle ⟨b, b.2, rfl⟩
  have := congrArg Subtype.val ((h P).is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  exact Subtype.ext (Subtype.ext this)

open scoped Pointwise in
theorem sylowTwoAbelian_quotient {G : Type*} [Group G] [Finite G] (h : SylowTwoAbelian G)
    (N : Subgroup G) [N.Normal] : SylowTwoAbelian (G ⧸ N) := by
  intro Q
  have hsurj := QuotientGroup.mk'_surjective N
  obtain ⟨P0⟩ : Nonempty (Sylow 2 G) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ N) (Sylow.mapSurjective hsurj P0) Q
  have h1 : IsMulCommutative (Sylow.mapSurjective hsurj P0 : Subgroup (G ⧸ N)) := by
    refine isMulCommutative_of_surjective (K := (P0 : Subgroup G)) ?_ ?_ (h P0)
    · exact ((QuotientGroup.mk' N).comp (P0 : Subgroup G).subtype).codRestrict _ (fun x => by
        rw [Sylow.coe_mapSurjective]; exact ⟨x, x.2, rfl⟩)
    · rintro ⟨y, hy⟩
      rw [Sylow.coe_mapSurjective] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have h2 : (Q : Subgroup (G ⧸ N)) =
      ConjAct.toConjAct g • (Sylow.mapSurjective hsurj P0 : Subgroup (G ⧸ N)) := by
    rw [← hg]; rfl
  rw [h2]
  exact isMulCommutative_of_injective
    (Subgroup.equivSMul (ConjAct.toConjAct g) _).symm.toMonoidHom
    (Subgroup.equivSMul (ConjAct.toConjAct g) _).symm.injective h1

end CFSGOutside.Arad
