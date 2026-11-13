import Mathlib
import CFSGOutside.WittDesigns.AutS5612.Hexads
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-!
# `Aut S(5,6,12) = M12`, and `M12` is sharply 5-transitive

Combining the 5-transitivity of `M12` with the corpus classification of 5-transitive groups of degree at most
80, the group of permutations preserving the Steiner system `S(5,6,12)` is exactly `M12`, of order 95040, and
the order of `M12` is derived rather than assumed.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm
open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

theorem five_transitive_cases (P : Subgroup (Equiv.Perm (Fin 12)))
    (hP : MulAction.IsMultiplyPretransitive P (Fin 12) 5) :
    P = ⊤ ∨ P = alternatingGroup (Fin 12) ∨ Nat.card P = 95040 := by
  have h := SubgroupCardClassificationOfCardLeEighty.subgroup_card_classification_of_card_le_eighty 12 (Fin 12) P
    (by simp) (by norm_num) (by norm_num) hP
  have hcard : Nat.card (Equiv.Perm (Fin 12)) = (12).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp
  rcases h with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · left
    exact (Subgroup.card_eq_iff_eq_top P).1 (h.trans hcard.symm)
  · right; left
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have := Subgroup.card_mul_index P
    rw [h, hcard] at this
    have h2 : (12).factorial / 2 * 2 = (12).factorial := Nat.div_mul_cancel (by decide)
    have : (12).factorial / 2 * P.index = (12).factorial / 2 * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by have := Nat.factorial_pos 12; omega) this
  · right; right; exact h
  · omega

theorem isMultiplyPretransitive_of_le_subgroup {G H : Subgroup (Equiv.Perm (Fin 12))} (hGH : G ≤ H)
    {n : ℕ} (h : MulAction.IsMultiplyPretransitive G (Fin 12) n) :
    MulAction.IsMultiplyPretransitive H (Fin 12) n := by
  refine MulAction.isMultiplyPretransitive_iff.2 fun x y => ?_
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.1 h x y
  exact ⟨⟨g.1, hGH g.2⟩, hg⟩

theorem card_autHexads : Nat.card autHexads = 95040 := by
  have h5 := isMultiplyPretransitive_of_le_subgroup m12_le_autHexads m12_five_transitive
  rcases five_transitive_cases autHexads h5 with h | h | h
  · exact absurd (h ▸ trivial : threeCycle ∈ autHexads) threeCycle_not_mem
  · exact absurd (h ▸ threeCycle_even) threeCycle_not_mem
  · exact h

/-- The group of permutations preserving the hexads of `S(5,6,12)` is `M12`. -/
theorem autHexads_eq_m12 : autHexads = M12 := by
  have h5 := m12_five_transitive
  have hle := m12_le_autHexads
  rcases five_transitive_cases M12 h5 with h | h | h
  · exact absurd (h ▸ trivial : threeCycle ∈ M12) (fun hm => threeCycle_not_mem (hle hm))
  · exact absurd (hle (h ▸ threeCycle_even)) threeCycle_not_mem
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h, card_autHexads])).symm

/-- `Aut S(5,6,12)` is sharply 5-transitive of order 95040. -/
theorem aut_hexads_sharply_five_transitive :
    IsSteiner56 hexads ∧ MulAction.IsMultiplyPretransitive autHexads (Fin 12) 5 ∧
      Nat.card autHexads = (12).descFactorial 5 := by
  refine ⟨hexads_steiner, ?_, by rw [card_autHexads]; decide⟩
  rw [autHexads_eq_m12]; exact m12_five_transitive

end CFSGOutside.WittDesigns.Witt5612
