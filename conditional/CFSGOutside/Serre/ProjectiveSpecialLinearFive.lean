import CFSGOutside.Serre.SimpleOrderSixty

/-!
# `PSL₂(𝔽₅)` has order sixty and is isomorphic to `A₅`

Used for Serre (2013), Théorème 5 (§6.4): the group `A₅ ≅ PSL₂(𝔽₅)` of order sixty is a group of Lie type in
characteristic five that the TauCeti catalogue lists as an alternating group. The order is computed by
transporting to `ZMod 5` along a ring isomorphism and counting the matrices of determinant one by kernel
reduction; the isomorphism with `A₅` is `nonempty_mulEquiv_alternatingGroup_five_of_card_sixty`.
-/

namespace CFSGOutside.Serre

open Matrix

/-- A field with five elements is isomorphic to `ZMod 5`. -/
theorem exists_ringEquiv_zmod_five (k : Type) [Field k] [Finite k] (hk : Nat.card k = 5) :
    Nonempty (k ≃+* ZMod 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fintype k := Fintype.ofFinite k
  have hc : Fintype.card k = Fintype.card (ZMod 5) := by
    rw [← Nat.card_eq_fintype_card, hk, ZMod.card]
  exact ⟨FiniteField.ringEquivOfCardEq hc⟩

/-- A field with five elements has exactly `120` matrices of determinant one in degree two. -/
theorem card_specialLinearGroup_two_of_card_five (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 5) : Nat.card (SpecialLinearGroup (Fin 2) k) = 120 := by
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five k hk
  have hdet : Nat.card (SpecialLinearGroup (Fin 2) k) =
      Nat.card (SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.mapMatrix.toEquiv fun M => ?_)
    have := RingHom.map_det e.toRingHom M
    simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, RingEquiv.mapMatrix_apply]
    change M.det = 1 ↔ (e.toRingHom.mapMatrix M).det = 1
    rw [← this]
    exact (map_eq_one_iff e e.injective).symm
  rw [hdet]
  change Nat.card {M : Matrix (Fin 2) (Fin 2) (ZMod 5) // M.det = 1} = 120
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The center of `SL₂(k)` for a field `k` with five elements has two elements, `±1`. -/
theorem card_center_specialLinearGroup_two_of_card_five (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 5) : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) k)) = 2 := by
  obtain ⟨e⟩ := exists_ringEquiv_zmod_five k hk
  rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := k)).toEquiv,
    Nat.card_congr (e.toMulEquiv.restrictRootsOfUnity _).toEquiv]
  have h : Nat.card (rootsOfUnity (max (Fintype.card (Fin 2)) 1) (ZMod 5)) =
      Nat.card {u : (ZMod 5)ˣ // u ^ 2 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u => mem_rootsOfUnity _ u)
  rw [h, Nat.card_eq_fintype_card]
  decide

/-- The projective special linear group of degree two over a field with five elements has order sixty. -/
theorem card_projectiveSpecialLinearGroup_two_of_card_five (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 5) : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) k) = 60 := by
  have h : Nat.card (SpecialLinearGroup (Fin 2) k) =
      Nat.card (ProjectiveSpecialLinearGroup (Fin 2) k) *
        Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) k)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_specialLinearGroup_two_of_card_five k hk, card_center_specialLinearGroup_two_of_card_five k hk]
    at h
  omega

/-- `PSL₂(𝔽₅)` is isomorphic to the alternating group on five letters. -/
theorem nonempty_projectiveSpecialLinearGroup_two_zmod_five_mulEquiv_alternatingGroup :
    Nonempty (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  have hk : Nat.card (ZMod 5) = 5 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hk]; norm_num)
  exact nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_projectiveSpecialLinearGroup_two_of_card_five (ZMod 5) hk)

end CFSGOutside.Serre
