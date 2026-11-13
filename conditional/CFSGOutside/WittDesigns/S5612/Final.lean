import Mathlib
import CFSGOutside.Corpus.SubgroupCardClassificationOfCardLeEighty
import CFSGOutside.WittDesigns.S5612.Unique
import CFSGOutside.WittDesigns.S5612.Defs

namespace CFSGOutside.WittDesigns.Witt5612

open Pointwise Equiv Equiv.Perm MulAction

open CFSGOutside.Corpus

variable [SubgroupCardClassificationOfCardLeEighty]

theorem smul_eq_map (σ : Perm (Fin 12)) (C : Finset (Fin 12)) : σ • C = C.map σ.toEmbedding := by
  refine Finset.ext fun x => ?_
  rw [Finset.mem_smul_finset, Finset.mem_map]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩

theorem steiner_transport {Ω : Type*} [DecidableEq Ω] (e : Ω ≃ Fin 12) {𝒯 : Finset (Finset Ω)}
    (h : IsSteiner 𝒯) : IsSteiner56 (𝒯.map e.finsetCongr.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.1 hC
    simp only [Equiv.coe_toEmbedding, Equiv.finsetCongr_apply, Finset.card_map]
    exact h.1 B hB
  · intro s hs
    obtain ⟨s0, rfl⟩ := e.finsetCongr.surjective s
    have hs0 : s0.card = 5 := by
      rw [Equiv.finsetCongr_apply, Finset.card_map] at hs
      exact hs
    obtain ⟨B, ⟨hB, hsB⟩, hu⟩ := h.2 _ hs0
    refine ⟨e.finsetCongr B, ⟨Finset.mem_map_of_mem _ hB, ?_⟩, ?_⟩
    · simp only [Equiv.finsetCongr_apply, Finset.map_subset_map]
      exact hsB
    · rintro C ⟨hC, hsC⟩
      obtain ⟨B', hB', rfl⟩ := Finset.mem_map.1 hC
      have hsC' : e.finsetCongr s0 ⊆ e.finsetCongr B' := hsC
      simp only [Equiv.finsetCongr_apply, Finset.map_subset_map] at hsC'
      have := hu B' ⟨hB', hsC'⟩
      show e.finsetCongr B' = e.finsetCongr B
      rw [this]

theorem mem_transport {Ω : Type*} [DecidableEq Ω] (e : Ω ≃ Fin 12) (𝒯 : Finset (Finset Ω))
    (B : Finset Ω) : e.finsetCongr B ∈ 𝒯.map e.finsetCongr.toEmbedding ↔ B ∈ 𝒯 := by
  exact Finset.mem_map' e.finsetCongr.toEmbedding

/-- **Witt (1938).** Any two Steiner systems `S(5,6,12)` are isomorphic. -/
theorem witt_S5612_unique_of_count
    (hcount : (go fiveMasks (addCov 0 123) [123]).length = 720)
    {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    (hΩ : Fintype.card Ω = 12) (hΩ' : Fintype.card Ω' = 12)
    {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : IsSteiner 𝒯) (h' : IsSteiner 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' := by
  classical
  let e : Ω ≃ Fin 12 := Fintype.equivFinOfCardEq hΩ
  let e' : Ω' ≃ Fin 12 := Fintype.equivFinOfCardEq hΩ'
  obtain ⟨σ, hσ⟩ := witt_fin12 hcount (steiner_transport e h) (steiner_transport e' h')
  refine ⟨e.trans (σ.trans e'.symm), fun B => ?_⟩
  rw [← mem_transport e, ← mem_transport e' 𝒯' (B.map (e.trans (σ.trans e'.symm)).toEmbedding), ← hσ]
  have : e'.finsetCongr (B.map (e.trans (σ.trans e'.symm)).toEmbedding) = σ • e.finsetCongr B := by
    rw [smul_eq_map, Equiv.finsetCongr_apply, Equiv.finsetCongr_apply, Finset.map_map, Finset.map_map]
    have hemb : (e.trans (σ.trans e'.symm)).toEmbedding.trans e'.toEmbedding =
        e.toEmbedding.trans σ.toEmbedding := Function.Embedding.ext fun x => by simp
    rw [hemb]
  rw [this, Finset.smul_mem_smul_finset_iff]

end CFSGOutside.WittDesigns.Witt5612
