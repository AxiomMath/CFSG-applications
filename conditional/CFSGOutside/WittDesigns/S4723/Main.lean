import Mathlib
import CFSGOutside.WittDesigns.S4723.Normal
import CFSGOutside.WittDesigns.S4723.Swap

/-!
# Witt (1938): the Steiner system `S(4,7,23)` is unique

Any two Steiner systems `S(4,7,23)` are isomorphic. The proof derives each system at a point, which by the
corpus theorem on the uniqueness of `S(3,6,22)` is the system of hexads. The blocks missing the point are
then one class of the odd heptads of the hexads, and an outer automorphism of the hexads exchanges the
two classes.
-/

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u v

namespace CFSGOutside.WittDesigns.Witt4723

open CFSGOutside.Corpus CFSGOutside.Corpus.WittDesign
open CFSGOutside.WittDesigns.Witt5824 (IsOddSeven)
attribute [local instance] Classical.propDecidable

variable [SteinerTripleIso.{0, 0}] [IsSteinerTripleHexads] [IsSteinerTripleCardInter.{0}] [CardHexads] [CardHexadAut]

theorem oddSeven_of_map {X : Finset (Fin 22)} (hX : IsOddSeven (X.map aPerm.toEmbedding)) :
    IsOddSeven X := by
  have := oddSeven_map hX
  rwa [map_a_a] at this

theorem iso_of_normal {𝒯₁ 𝒯₂ : Finset (Finset P23)} (h₁ : IsNormal 𝒯₁) (h₂ : IsNormal 𝒯₂) :
    ∃ σ : Equiv.Perm P23, σ Q = Q ∧ ∀ B, B ∈ 𝒯₁ ↔ B.map σ.toEmbedding ∈ 𝒯₂ := by
  obtain ⟨Y0, hY0⟩ := exists_noQ h₁
  obtain ⟨Y0', hY0'⟩ := exists_noQ h₂
  have o0 := isOddSeven_of_mem h₁ hY0
  have o0' := isOddSeven_of_mem h₂ hY0'
  by_cases hk : Kin Y0 Y0'
  · refine ⟨Equiv.refl _, rfl, fun B => ?_⟩
    have hB : B.map (Equiv.refl P23).toEmbedding = B := by ext x; simp
    rw [hB, mem_iff_full h₁ hY0, mem_iff_full h₂ hY0']
    refine or_congr Iff.rfl (and_congr Iff.rfl ⟨fun ⟨h, h'⟩ => ⟨h, ?_⟩, fun ⟨h, h'⟩ => ⟨h, ?_⟩⟩)
    · exact Kin.trans h o0 o0' h' hk
    · exact Kin.trans h o0' o0 h' hk.symm
  · let σ : Equiv.Perm P23 := Equiv.sumCongr aPerm (Equiv.refl Unit)
    have hσQ : σ Q = Q := by simp [σ, Q]
    have hσQ' : σ.symm Q = Q := by simp [σ, Q]
    refine ⟨σ, hσQ, fun B => ?_⟩
    have hQ : Q ∈ B.map σ.toEmbedding ↔ Q ∈ B := by
      rw [Finset.mem_map_equiv, hσQ']
    have hL : lift (B.map σ.toEmbedding) = (lift B).map aPerm.toEmbedding := by
      ext x
      rw [mem_lift, Finset.mem_map_equiv, Finset.mem_map_equiv, mem_lift]
      simp [σ]
    rw [mem_iff_full h₁ hY0, mem_iff_full h₂ hY0', hQ, hL]
    refine or_congr (and_congr Iff.rfl (aPerm_iff _).symm) (and_congr Iff.rfl ⟨fun ⟨h, h'⟩ => ⟨oddSeven_map h, swap_ok o0 o0' hk h h'⟩, fun ⟨h, h'⟩ => ?_⟩)
    have hX := oddSeven_of_map h
    refine ⟨hX, ?_⟩
    have := swap_ok o0' o0 (fun e => hk e.symm) h h'
    rwa [map_a_a] at this

/-- **Witt (1938).** Any two Steiner systems `S(4,7,23)` are isomorphic. -/
theorem witt_S4723_unique {Ω : Type u} {Ω' : Type v} [SteinerTripleIso.{u, 0}] [SteinerTripleIso.{v, 0}]
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω']
    [DecidableEq Ω'] {𝒯 : Finset (Finset Ω)} {𝒯' : Finset (Finset Ω')} (h : IsSteiner4 𝒯)
    (h' : IsSteiner4 𝒯') :
    ∃ f : Ω ≃ Ω', ∀ B : Finset Ω, B ∈ 𝒯 ↔ B.map f.toEmbedding ∈ 𝒯' := by
  obtain ⟨φ, hφ⟩ := exists_normal h
  obtain ⟨φ', hφ'⟩ := exists_normal h'
  obtain ⟨σ, -, hσ⟩ := iso_of_normal hφ hφ'
  refine ⟨φ.trans (σ.trans φ'.symm), fun B => ?_⟩
  have h1 : B ∈ 𝒯 ↔ B.map φ.toEmbedding ∈ 𝒯.image fun B => B.map φ.toEmbedding := by
    rw [mem_image_map]; simp [Finset.map_map]
  rw [h1, hσ]
  have h2 := mem_image_map (𝒯 := 𝒯') φ' (X := (B.map φ.toEmbedding).map σ.toEmbedding)
  rw [h2]
  simp [Finset.map_map]
  rfl

end CFSGOutside.WittDesigns.Witt4723
