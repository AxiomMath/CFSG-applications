import Mathlib
import CFSGOutside.Corpus.IsMultiplyPretransitiveM22
import CFSGOutside.Corpus.M22Simple

/-!
A subgroup of `M22` such that the product of any two elements outside it lies in it, is all of `M22`.
Such a subgroup has index at most two, so it is normal, and `M22` is simple and has more than two elements.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.M24Five

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign

variable [IsMultiplyPretransitiveM22] [M22Simple]

theorem m22_eq_top_of_mul (H : Subgroup M22) (hmul : ∀ a b : M22, a ∉ H → b ∉ H → b * a ∈ H) :
    H = ⊤ := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun b => ?_⟩
    by_cases hb : b ∈ H
    · exact Or.inr ⟨hb, fun h => ha (by simpa using mul_mem (inv_mem hb) h)⟩
    · exact Or.inl ⟨hmul a b ha hb, hb⟩
  haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
  haveI : Finite M22 := (M22Simple.fam_m22_simplicity).1
  haveI : IsSimpleGroup M22 := (M22Simple.fam_m22_simplicity).2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · rw [h, Subgroup.index_bot] at hidx
    let e0 : Fin 3 ↪ Fin 22 := ⟨![0, 1, 2], by decide⟩
    have hsurj : Function.Surjective (fun m : M22 => m • e0) := fun e =>
      MulAction.isMultiplyPretransitive_iff.1 IsMultiplyPretransitiveM22.isMultiplyPretransitive_M22 e0 e
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hidx, Nat.card_eq_fintype_card, Fintype.card_embedding_eq] at this
    simp at this
  · rw [h, Subgroup.index_top] at hidx
    omega

end CFSGOutside.WittDesigns.M24Five
