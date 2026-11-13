import Mathlib
import CFSGOutside.WittDesigns.M24FiveTransitive.Main
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty

/-!
# The 5-transitive subgroups of `Sym(24)`

Combining 5-transitivity of the automorphism group of `S(5,8,24)` with the corpus classification of
5-transitive groups of degree at most 80, every 5-transitive subgroup of `Sym(24)` is `Sym(24)`, `Alt(24)`
or has the order of `Aut S(5,8,24)`, and all three orders occur.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.M24Five

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign

variable [SubgroupCardClassificationOfCardLeEighty]

theorem five_transitive_cases {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 24)
    (P : Subgroup (Equiv.Perm Ω)) (hP : MulAction.IsMultiplyPretransitive P Ω 5) :
    P = ⊤ ∨ P = alternatingGroup Ω ∨ Nat.card P = 244823040 := by
  have h := SubgroupCardClassificationOfCardLeEighty.subgroup_card_classification_of_card_le_eighty 24 Ω P hΩ (by norm_num)
    (by norm_num) hP
  have hcard : Nat.card (Equiv.Perm Ω) = (24).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hΩ]
  rcases h with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · left
    exact (Subgroup.card_eq_iff_eq_top P).1 (h.trans hcard.symm)
  · right; left
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have := Subgroup.card_mul_index P
    rw [h, hcard] at this
    have hpos : 0 < (24).factorial := Nat.factorial_pos 24
    have h2 : (24).factorial / 2 * 2 = (24).factorial := Nat.div_mul_cancel (by decide)
    have : (24).factorial / 2 * P.index = (24).factorial / 2 * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by have := Nat.factorial_pos 24; omega) this
  · omega
  · right; right; exact h

theorem isMultiplyPretransitive_of_le_subgroup {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {G H : Subgroup (Equiv.Perm Ω)} (hGH : G ≤ H) {n : ℕ} (h : MulAction.IsMultiplyPretransitive G Ω n) :
    MulAction.IsMultiplyPretransitive H Ω n := by
  refine MulAction.isMultiplyPretransitive_iff.2 fun x y => ?_
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.1 h x y
  exact ⟨⟨g.1, hGH g.2⟩, hg⟩

end CFSGOutside.WittDesigns.M24Five
