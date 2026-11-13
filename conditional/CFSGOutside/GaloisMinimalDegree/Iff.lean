import CFSGOutside.GaloisMinimalDegree.Converse
import CFSGOutside.GaloisMinimalDegree.Minimal

open scoped MatrixGroups

namespace CFSGOutside.GaloisMinimalDegree

open CFSGOutside.Corpus CFSGOutside.Psl2Basic

set_option maxHeartbeats 2000000 in
lemma exists_index_eq_of_mem {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) :
    ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ ∧ H.index = p := by
  have := Fintype.ofFinite F
  have e : ZMod p ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card (α := F), hF])
  obtain ⟨H, hne, hidx⟩ : ∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)),
      H ≠ ⊤ ∧ H.index = p := by
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [exists_index_2, exists_index_3, exists_index_5, exists_index_7, exists_index_11]
  have hidx' : (H.map (pslEquiv e).toMonoidHom).index = p := by
    exact (Subgroup.index_map_equiv H (pslEquiv e)).trans hidx
  refine ⟨H.map (pslEquiv e).toMonoidHom, fun h => ?_, hidx'⟩
  rw [h, Subgroup.index_top] at hidx'
  have := (inferInstance : Fact p.Prime).out.two_le
  omega

theorem galois_iff [DicksonPsl2SubgroupClassification.{0}] {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    (∃ H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), H ≠ ⊤ ∧ H.index < p + 1) ↔
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  constructor
  · rintro ⟨H, hne, hidx⟩
    have := galois_minimal_degree (f := 1) (by rw [hF, pow_one]) H hne (by rw [hF]; omega)
    rw [hF] at this
    rcases this with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · subst h; exact absurd (inferInstance : Fact (Nat.Prime 9)).out (by norm_num)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · intro hp
    obtain ⟨H, hne, hidx⟩ := exists_index_eq_of_mem hF hp
    exact ⟨H, hne, by omega⟩

end CFSGOutside.GaloisMinimalDegree
