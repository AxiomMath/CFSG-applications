import Mathlib
import CFSGOutside.WittDesigns.S5824.Main

/-!
Normalizing an `S(5,8,24)` at a chosen pair of points, and comparing two normalized systems by a
permutation that fixes the 22 ordinary points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Aut5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.PlessSloaneG22 CFSGOutside.WittDesigns.Witt5824
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

theorem exists_normal_at {Ω : Type u} [SteinerTripleIso.{u, 0}] [Fintype Ω] [DecidableEq Ω] {𝒮 : Finset (Finset Ω)}
    (h : IsSteiner5 𝒮) {p q : Ω} (hpq : p ≠ q) :
    ∃ φ : Ω ≃ Pt, φ p = Sum.inr false ∧ φ q = Sum.inr true ∧
      IsNormal (𝒮.image fun B => B.map φ.toEmbedding) := by
  obtain ⟨e, he⟩ := SteinerTripleIso.steinerTriple_iso (isSteinerTriple_derived h hpq) IsSteinerTripleHexads.isSteinerTriple_hexads
  refine ⟨toPt hpq e, toPt_p hpq e, toPt_q hpq e, h.image _, fun H => ?_⟩
  rw [mem_image_map]
  have key : (hexBlk H).map (toPt hpq e).symm.toEmbedding =
      insert p (insert q ((H.map e.symm.toEmbedding).map (Function.Embedding.subtype _))) := by
    ext x
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
    by_cases hxp : x = p
    · subst hxp; simp [toPt_p, hexBlk]
    by_cases hxq : x = q
    · subst hxq; simp [toPt_q, hexBlk, blk]
    · have hx : toPt hpq e x = Sum.inl (e ⟨x, hxp, hxq⟩) := toPt_rest hpq e ⟨x, hxp, hxq⟩
      rw [hx]
      simp [hexBlk, blk, ι, hxp, hxq]
  rw [key]
  have hH : (H.map e.symm.toEmbedding).map e.toEmbedding = H := by simp [Finset.map_map]
  have := he (H.map e.symm.toEmbedding)
  rw [hH] at this
  rw [← this, derived, Finset.mem_filter]
  simp

theorem iso_of_normal' {𝒮₁ 𝒮₂ : Finset (Finset Pt)} (h₁ : IsNormal 𝒮₁) (h₂ : IsNormal 𝒮₂) :
    ∃ σ : Equiv.Perm Pt, (∀ i : Fin 22, σ (Sum.inl i) = Sum.inl i) ∧
      ∀ B, B ∈ 𝒮₁ ↔ B.map σ.toEmbedding ∈ 𝒮₂ := by
  rcases classes h₁ h₂ with ⟨hf, ht⟩ | ⟨hf, ht⟩
  · refine ⟨Equiv.refl _, fun i => rfl, fun B => ?_⟩
    rw [mem_iff h₁ B, mem_iff h₂ (B.map (Equiv.refl Pt).toEmbedding), hf, ht]
    simp
  · refine ⟨swapPt, fun i => by simp [swapPt, Equiv.swap_apply_of_ne_of_ne], fun B => ?_⟩
    rw [mem_iff h₁ B, mem_iff h₂ (B.map swapPt.toEmbedding), hf, ht, Phi, Phi, lift_map_swap]
    have e1 : (Sum.inr false : Pt) ∈ B.map swapPt.toEmbedding ↔ (Sum.inr true : Pt) ∈ B := by
      rw [mem_map_swap]; simp [swapPt]
    have e2 : (Sum.inr true : Pt) ∈ B.map swapPt.toEmbedding ↔ (Sum.inr false : Pt) ∈ B := by
      rw [mem_map_swap]; simp [swapPt]
    rw [e1, e2]
    constructor
    · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
      · exact Or.inl ⟨b, a, c⟩
      · exact Or.inr (Or.inr (Or.inl ⟨b, a, c⟩))
      · exact Or.inr (Or.inl ⟨b, a, c⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨b, a, c⟩))
    · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩)
      · exact Or.inl ⟨b, a, c⟩
      · exact Or.inr (Or.inr (Or.inl ⟨b, a, c⟩))
      · exact Or.inr (Or.inl ⟨b, a, c⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨b, a, c⟩))

end CFSGOutside.WittDesigns.Aut5824
