import Mathlib
import CFSGOutside.WittDesigns.AutS5612.HexCheck

/-!
# The Steiner system `S(5,6,12)` and its automorphism group contains `M12`

Every 5-set lies in exactly one hexad, and the generators of `M12` permute the hexads.
-/

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm

def IsSteiner56 (𝒮 : Finset (Finset (Fin 12))) : Prop :=
  (∀ B ∈ 𝒮, B.card = 6) ∧ ∀ s : Finset (Fin 12), s.card = 5 → ∃! B, B ∈ 𝒮 ∧ s ⊆ B

theorem mem_hexads {B : Finset (Fin 12)} : B ∈ hexads ↔ ∃ m ∈ hexMasks, maskSet m = B := by
  unfold hexads
  rw [List.mem_toFinset, List.mem_map]




theorem mem_maskSet (m : ℕ) (i : Fin 12) : i ∈ maskSet m ↔ m.testBit i.val = true := by
  simp [maskSet]

theorem exists_mask (s : Finset (Fin 12)) : ∃ m, m < 4096 ∧ maskSet m = s := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by norm_num, by ext i; rw [mem_maskSet]; simp⟩
  | insert a s _ ih =>
    obtain ⟨m, hm, rfl⟩ := ih
    refine ⟨m ||| 2 ^ a.val, ?_, ?_⟩
    · have : 2 ^ a.val < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) a.2
      exact Nat.or_lt_two_pow (by simpa using hm) this
    · ext i
      rw [mem_maskSet, Finset.mem_insert, mem_maskSet, Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (Fin.ext h).symm
      · rintro (rfl | h)
        · exact Or.inr rfl
        · exact Or.inl h

theorem hexads_card_six : ∀ B ∈ hexads, B.card = 6 := by
  intro B hB
  obtain ⟨m, hm, rfl⟩ := mem_hexads.1 hB
  exact hexMasks_card m hm

theorem hexads_steiner : IsSteiner56 hexads := by
  refine ⟨hexads_card_six, fun s hs => ?_⟩
  obtain ⟨m, hm, rfl⟩ := exists_mask s
  obtain ⟨m0, hm0⟩ := List.length_eq_one_iff.1 (steiner_check m hm hs)
  have hmem : m0 ∈ hexMasks.filter fun m2 => maskSet m ⊆ maskSet m2 := by rw [hm0]; simp
  rw [List.mem_filter] at hmem
  refine ⟨maskSet m0, ⟨mem_hexads.2 ⟨m0, hmem.1, rfl⟩, by simpa using hmem.2⟩, ?_⟩
  rintro B ⟨hB, hsB⟩
  obtain ⟨m1, hm1, rfl⟩ := mem_hexads.1 hB
  have : m1 ∈ hexMasks.filter fun m2 => maskSet m ⊆ maskSet m2 := List.mem_filter.2 ⟨hm1, by simpa using hsB⟩
  rw [hm0] at this
  simp at this
  rw [this]

theorem smul_hexads_of_check {g : Equiv.Perm (Fin 12)} (h : permCheck g = true) : g • hexads = hexads := by
  have hsub : g • hexads ⊆ hexads := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.1 hx
    obtain ⟨m, hm, rfl⟩ := mem_hexads.1 hB
    simp only [permCheck, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨m2, hm2, h2⟩ := h m hm
    exact mem_hexads.2 ⟨m2, hm2, h2.symm⟩
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

def autHexads : Subgroup (Equiv.Perm (Fin 12)) := MulAction.stabilizer (Equiv.Perm (Fin 12)) hexads

theorem m12_le_autHexads : M12 ≤ autHexads := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact smul_hexads_of_check permCheck_a
  · exact smul_hexads_of_check permCheck_b

theorem threeCycle_even : threeCycle ∈ alternatingGroup (Fin 12) := by
  simp [threeCycle, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]


theorem threeCycle_not_mem : threeCycle ∉ autHexads := by
  intro h
  have h1 : threeCycle • hexads = hexads := h
  have h123 : maskSet 123 ∈ hexads := mem_hexads.2 ⟨123, by decide +kernel, rfl⟩
  have : threeCycle • maskSet 123 ∈ hexads := h1 ▸ Finset.smul_mem_smul_finset h123
  obtain ⟨m2, hm2, h2⟩ := mem_hexads.1 this
  exact threeCycle_moves m2 hm2 h2.symm

end CFSGOutside.WittDesigns.Witt5612
