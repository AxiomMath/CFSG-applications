import CFSGOutside.AndersenOliverVentura.Defs

/-!
# AOV tameness: `O^p` of a group with a central Sylow `p`-subgroup

If a Sylow `p`-subgroup `Z` of a finite group `C` is central, then `O^p(C)` is a normal complement
of `Z` of order prime to `p` (Burnside's normal `p`-complement theorem).
-/

namespace AndersenOliverVentura.Tame

open Subgroup

universe u

variable {C : Type u} [Group C] [Finite C] {p : ℕ} [hp : Fact p.Prime]

lemma oP_eq_ker_transferSylow (Z : Sylow p C) (hZ : (Z : Subgroup C) ≤ center C) :
    FusionSystem.oP p C =
      (MonoidHom.transferSylow Z (fun x _ => by
        rw [mem_centralizer_iff]; intro y hy; exact (mem_center_iff.1 (hZ hy) x).symm)).ker := by
  set hP : normalizer (Z : Set C) ≤ centralizer (Z : Set C) := fun x _ => by
    rw [mem_centralizer_iff]; intro y hy; exact (mem_center_iff.1 (hZ hy) x).symm
  set K := (MonoidHom.transferSylow Z hP).ker
  have hc := MonoidHom.ker_transferSylow_isComplement' Z hP
  have hK : ¬ p ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow Z hP
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    obtain ⟨k, hk⟩ := Z.isPGroup'.exists_card_eq
    exact ⟨k, hc.symm.index_eq_card.trans hk⟩
  · intro x hx
    rw [FusionSystem.oP, mem_sInf]
    rintro N ⟨hN, k, hk⟩
    have h1 : x ^ N.index ∈ N := N.pow_index_mem x
    have hcop : (N.index).Coprime (orderOf x) := by
      rw [hk]
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hd
      apply hK
      exact hd.trans (by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : K)
        rwa [orderOf_mk] at this)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact N.pow_mem h1 m

end AndersenOliverVentura.Tame

namespace AndersenOliverVentura.Tame

open Subgroup

variable {C : Type*} [Group C] [Finite C] {p : ℕ} [hp : Fact p.Prime]

/-- If a Sylow `p`-subgroup `Z` of `C` is central, then every element is `k * z` with
`k ∈ O^p(C)` and `z ∈ Z`, and `O^p(C)` has order prime to `p`. -/
lemma oP_complement (Z : Sylow p C) (hZ : (Z : Subgroup C) ≤ center C) :
    (∀ c : C, ∃ k ∈ FusionSystem.oP p C, ∃ z ∈ (Z : Subgroup C), c = k * z) ∧
      ¬ p ∣ Nat.card (FusionSystem.oP p C) := by
  rw [oP_eq_ker_transferSylow Z hZ]
  refine ⟨fun c => ?_, MonoidHom.not_dvd_card_ker_transferSylow _ _⟩
  obtain ⟨⟨k, z⟩, hkz, -⟩ := (MonoidHom.ker_transferSylow_isComplement' Z _).existsUnique c
  exact ⟨k, k.2, z, z.2, hkz.symm⟩

end AndersenOliverVentura.Tame
