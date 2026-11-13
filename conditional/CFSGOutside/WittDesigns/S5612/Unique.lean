import Mathlib
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty
import CFSGOutside.WittDesigns.S5612.Orbit

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm MulAction

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

def stabHexT : Type := {σ : Perm (Fin 12) // σ • blockZero = blockZero ∧ σ • hexads = hexads}

def equivStabG : ↥(stabilizer (stabilizer (Perm (Fin 12)) blockZero) hexads) ≃
    {σ : Perm (Fin 12) // σ • blockZero = blockZero ∧ σ • hexads = hexads} where
  toFun x := ⟨x.1.1, mem_stabilizer_iff.1 x.1.2, mem_stabilizer_iff.1 x.2⟩
  invFun σ := ⟨⟨σ.1, mem_stabilizer_iff.2 σ.2.1⟩, mem_stabilizer_iff.2 σ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def equivStabAut : ↥(stabilizer autHexads blockZero) ≃
    {σ : Perm (Fin 12) // σ • blockZero = blockZero ∧ σ • hexads = hexads} where
  toFun x := ⟨x.1.1, mem_stabilizer_iff.1 x.2, mem_stabilizer_iff.1 x.1.2⟩
  invFun σ := ⟨⟨σ.1, mem_stabilizer_iff.2 σ.2.2⟩, mem_stabilizer_iff.2 σ.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_stab_pair :
    Nat.card (stabilizer (stabilizer (Perm (Fin 12)) blockZero) hexads) = 720 := by
  rw [Nat.card_congr (equivStabG.trans equivStabAut.symm), card_stab_aut]

def lset : Finset (Finset (Finset (Fin 12))) :=
  ((go fiveMasks (addCov 0 123) [123]).map fun L => (L.map maskSet).toFinset).toFinset

theorem mem_lset {𝒮 : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) (hB : blockZero ∈ 𝒮) :
    𝒮 ∈ lset := by
  have hc : (maskSet 123).card = 6 := hexads_card_six _ blockZero_mem
  have hb0 : ∀ t, t < 4096 → (maskSet t).card = 5 →
      ((0 : ℕ).testBit t = true ↔ ∃ m ∈ ([] : List ℕ), maskSet t ⊆ maskSet m) := by
    intro t _ _; simp
  obtain ⟨L, hL, -, hLe⟩ := go_sound h fiveMasks [] (addCov 0 123) [123] (by simp)
    (by intro m hm; simp at hm; subst hm; exact ⟨by norm_num, hB⟩)
    (cov_step hb0 (by norm_num) hc) (by simp)
  unfold lset
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨L, hL, hLe⟩

theorem orbit_of_contains (hcount : (go fiveMasks (addCov 0 123) [123]).length = 720)
    {𝒮 : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) (hB : blockZero ∈ 𝒮) :
    ∃ g : Perm (Fin 12), g • blockZero = blockZero ∧ g • hexads = 𝒮 := by
  have hlcard : lset.card ≤ 720 := by
    unfold lset
    exact (List.toFinset_card_le _).trans (by rw [List.length_map, hcount])
  have hsub : (orbit (stabilizer (Perm (Fin 12)) blockZero) hexads) ⊆ (lset : Set _) := by
    intro 𝒯 h𝒯
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 h𝒯
    have hg : g.1 • blockZero = blockZero := mem_stabilizer_iff.1 g.2
    refine Finset.mem_coe.2 (mem_lset ?_ ?_)
    · exact smul_steiner hexads_steiner g.1
    · have hm : g.1 • blockZero ∈ g.1 • hexads := Finset.smul_mem_smul_finset blockZero_mem
      rw [hg] at hm
      exact hm
  have hmul := orb_mul (stabilizer (Perm (Fin 12)) blockZero) hexads
  rw [card_stab_pair, card_stab_set] at hmul
  have hO : (orbit (stabilizer (Perm (Fin 12)) blockZero) hexads).ncard = 720 :=
    Nat.eq_of_mul_eq_mul_right (show 0 < 720 by norm_num) (hmul.trans (by norm_num))
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hO]; exact hlcard)
    (Finset.finite_toSet _)
  have hmem : 𝒮 ∈ (orbit (stabilizer (Perm (Fin 12)) blockZero) hexads) := by
    rw [heq]; exact Finset.mem_coe.2 (mem_lset h hB)
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 hmem
  exact ⟨g.1, mem_stabilizer_iff.1 g.2, hg⟩

theorem exists_block {𝒮 : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) : ∃ B, B ∈ 𝒮 := by
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 12))) (n := 5)
    (by simp)
  obtain ⟨B, ⟨hB, -⟩, -⟩ := h.2 s hs
  exact ⟨B, hB⟩

theorem normalize (hcount : (go fiveMasks (addCov 0 123) [123]).length = 720)
    {𝒮 : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) :
    ∃ τ : Perm (Fin 12), ∃ g : Perm (Fin 12), g • hexads = τ • 𝒮 := by
  obtain ⟨B, hB⟩ := exists_block h
  obtain ⟨τ, hτ⟩ := exists_perm_smul_eq (A := B) (A' := blockZero)
    (by rw [h.1 B hB, hexads_card_six _ blockZero_mem])
  obtain ⟨g, -, hg⟩ := orbit_of_contains hcount (smul_steiner h τ)
    (by rw [← hτ]; exact Finset.smul_mem_smul_finset hB)
  exact ⟨τ, g, hg⟩

/-- Any Steiner system `S(5,6,12)` on `Fin 12` is a translate of the hexads (given the search count). -/
theorem witt_fin12 (hcount : (go fiveMasks (addCov 0 123) [123]).length = 720)
    {𝒮 𝒮' : Finset (Finset (Fin 12))} (h : IsSteiner56 𝒮) (h' : IsSteiner56 𝒮') :
    ∃ σ : Perm (Fin 12), σ • 𝒮 = 𝒮' := by
  obtain ⟨τ, g, hg⟩ := normalize hcount h
  obtain ⟨τ', g', hg'⟩ := normalize hcount h'
  refine ⟨τ'⁻¹ * g' * g⁻¹ * τ, ?_⟩
  have e1 : g⁻¹ • (τ • 𝒮) = hexads := by rw [← hg, inv_smul_smul]
  calc (τ'⁻¹ * g' * g⁻¹ * τ) • 𝒮 = τ'⁻¹ • (g' • (g⁻¹ • (τ • 𝒮))) := by simp [mul_smul]
    _ = τ'⁻¹ • (g' • hexads) := by rw [e1]
    _ = τ'⁻¹ • (τ' • 𝒮') := by rw [hg']
    _ = 𝒮' := inv_smul_smul _ _

end CFSGOutside.WittDesigns.Witt5612
