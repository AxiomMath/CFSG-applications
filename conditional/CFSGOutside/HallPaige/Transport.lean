import CFSGOutside.HallPaige.Statements

/-!
# Transport along isomorphisms

`IsGood` and `ProperSubgroupsAdmissible` are invariant under group isomorphisms (in any universes).
-/

namespace CFSGOutside.HallPaige

variable {G H : Type*} [Group G] [Group H]

/-- Being good transfers along an isomorphism. -/
theorem IsGood.of_mulEquiv (e : G ≃* H) (hG : IsGood G) : IsGood H := by
  intro P
  let Q : Sylow 2 G := P.comapOfInjective e.toMonoidHom e.injective
    (by rw [MonoidHom.range_eq_top.mpr (show Function.Surjective e.toMonoidHom from e.surjective)]
        exact le_top)
  have hQ : (Q : Subgroup G) = (P : Subgroup H).comap e.toMonoidHom := rfl
  rcases hG Q with h | h
  · left
    rw [hQ] at h
    rw [eq_bot_iff]
    intro x hx
    have : e.symm x ∈ (P : Subgroup H).comap e.toMonoidHom := by simpa using hx
    rw [h] at this
    simpa using congrArg e ((Subgroup.mem_bot).mp this)
  · right
    intro hc
    apply h
    have e' : (Q : Subgroup G) ≃* (P : Subgroup H) :=
      (e.subgroupMap (Q : Subgroup G)).trans (MulEquiv.subgroupCongr (by
        rw [hQ]; exact Subgroup.map_comap_eq_self_of_surjective e.surjective _))
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

/-- `ProperSubgroupsAdmissible` transfers along an isomorphism. -/
theorem ProperSubgroupsAdmissible.of_mulEquiv (e : G ≃* H) (hG : ProperSubgroupsAdmissible G) :
    ProperSubgroupsAdmissible H := by
  intro K hK hgood
  let K' : Subgroup G := K.comap e.toMonoidHom
  have hmap : K'.map e.toMonoidHom = K := Subgroup.map_comap_eq_self_of_surjective e.surjective K
  let f : K' ≃* K := (e.subgroupMap K').trans (MulEquiv.subgroupCongr hmap)
  refine HasCompleteMapping.of_mulEquiv f (hG K' ?_ (IsGood.of_mulEquiv f.symm hgood))
  intro htop
  apply hK
  rw [← hmap, htop, Subgroup.map_top_of_surjective _ e.surjective]

end CFSGOutside.HallPaige
