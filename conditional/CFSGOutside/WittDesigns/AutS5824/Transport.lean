import Mathlib
import CFSGOutside.WittDesigns.AutS5824.Normalize
import CFSGOutside.Corpus.CardHexadAut

/-!
The automorphism group of a block system, transported along a bijection of the points.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSGOutside.WittDesigns.Aut5824

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign CFSGOutside.WittDesigns.Witt5824

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

theorem conj_mem {𝒮 : Finset (Finset Ω)} (φ : Ω ≃ Ω') {σ : Equiv.Perm Ω} (hσ : σ ∈ blockAut 𝒮) :
    φ.symm.trans (σ.trans φ) ∈ blockAut (𝒮.image fun B => B.map φ.toEmbedding) := by
  rw [mem_blockAut]
  intro B'
  rw [mem_image_map, mem_image_map]
  have : (B'.map (φ.symm.trans (σ.trans φ)).toEmbedding).map φ.symm.toEmbedding =
      (B'.map φ.symm.toEmbedding).map σ.toEmbedding := by
    ext x
    simp only [Finset.mem_map_equiv]
    simp
  rw [this]
  exact hσ _

theorem image_image_symm (𝒮 : Finset (Finset Ω)) (φ : Ω ≃ Ω') :
    (𝒮.image fun B => B.map φ.toEmbedding).image (fun B => B.map φ.symm.toEmbedding) = 𝒮 := by
  rw [Finset.image_image]
  have : ((fun B : Finset Ω' => B.map φ.symm.toEmbedding) ∘ fun B : Finset Ω => B.map φ.toEmbedding)
      = id := by
    funext B
    simp [Finset.map_map]
  rw [this, Finset.image_id]

theorem card_blockAut_image (𝒮 : Finset (Finset Ω)) (φ : Ω ≃ Ω') :
    Nat.card (blockAut (𝒮.image fun B => B.map φ.toEmbedding)) = Nat.card (blockAut 𝒮) := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => (⟨φ.symm.trans (σ.1.trans φ), conj_mem φ σ.2⟩ :
      blockAut (𝒮.image fun B => B.map φ.toEmbedding))) ⟨?_, ?_⟩)
  · intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have := congrArg (fun f : Equiv.Perm Ω' => f (φ x)) (congrArg Subtype.val h)
    simpa using this
  · intro τ
    refine ⟨⟨φ.trans (τ.1.trans φ.symm), ?_⟩, ?_⟩
    · have := conj_mem φ.symm τ.2
      rw [image_image_symm] at this
      exact this
    · apply Subtype.ext
      apply Equiv.ext
      intro x
      simp

end CFSGOutside.WittDesigns.Aut5824
