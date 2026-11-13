import CFSGOutside.HallPaige.Defs

/-!
# Good subgroups

* `CFSGOutside.HallPaige.isGood_of_index_odd`: a subgroup of odd index in a good finite group is good (it
  contains a Sylow 2-subgroup).
-/

namespace CFSGOutside.HallPaige

variable {G : Type*} [Group G] [Finite G]

/-- A subgroup of odd index in a good finite group is good: its Sylow 2-subgroups are Sylow
2-subgroups of the whole group. -/
theorem isGood_of_index_odd (hG : IsGood G) (H : Subgroup G) (hH : Odd H.index) : IsGood H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P
  let Q : Subgroup G := (P : Subgroup H).map H.subtype
  let e : (P : Subgroup H) ≃* Q := (P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  have hQcard : Nat.card Q = 2 ^ (Nat.card G).factorization 2 := by
    rw [← Nat.card_congr e.toEquiv, P.card_eq_multiplicity, ← H.card_mul_index,
      Nat.factorization_mul (Nat.card_pos (α := H)).ne' (Subgroup.index_ne_zero_of_finite)]
    have h2 : (H.index).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hH)
    simp [h2]
  let S : Sylow 2 G := Sylow.ofCard Q hQcard
  rcases hG S with h | h
  · left
    have : Q = ⊥ := h
    rw [Subgroup.eq_bot_iff_card] at this ⊢
    rw [Nat.card_congr e.toEquiv, this]
  · right
    intro hc
    exact h (by
      change IsCyclic Q
      exact isCyclic_of_surjective e.toMonoidHom e.surjective)

end CFSGOutside.HallPaige
